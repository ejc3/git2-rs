//! Git filter support for transforming file contents.
//!
//! Filters are used to transform file data during checkout (smudge) and
//! commit (clean) operations. The most common use case is Git LFS, which
//! uses filters to replace large file content with pointers.

use std::ffi::CString;
use std::marker;
use std::ptr;

use crate::util::Binding;
use crate::{raw, Blob, Buf, Error, Repository};

/// Direction of filter application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FilterMode {
    /// Convert from the Git object database to the working tree (smudge).
    ToWorktree,
    /// Convert from the working tree to the Git object database (clean).
    ToOdb,
}

impl FilterMode {
    fn raw(&self) -> raw::git_filter_mode_t {
        match self {
            FilterMode::ToWorktree => raw::GIT_FILTER_TO_WORKTREE,
            FilterMode::ToOdb => raw::GIT_FILTER_TO_ODB,
        }
    }
}

bitflags::bitflags! {
    /// Flags for filter loading.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct FilterFlags: u32 {
        /// Default filter flags.
        const DEFAULT = raw::GIT_FILTER_DEFAULT as u32;
        /// Don't error for safecrlf violations.
        const ALLOW_UNSAFE = raw::GIT_FILTER_ALLOW_UNSAFE as u32;
        /// Don't load /etc/gitattributes.
        const NO_SYSTEM_ATTRIBUTES = raw::GIT_FILTER_NO_SYSTEM_ATTRIBUTES as u32;
        /// Load attributes from .gitattributes in the root of HEAD.
        const ATTRIBUTES_FROM_HEAD = raw::GIT_FILTER_ATTRIBUTES_FROM_HEAD as u32;
        /// Load attributes from .gitattributes in a given commit.
        const ATTRIBUTES_FROM_COMMIT = raw::GIT_FILTER_ATTRIBUTES_FROM_COMMIT as u32;
    }
}

impl Default for FilterFlags {
    fn default() -> Self {
        FilterFlags::DEFAULT
    }
}

/// A list of filters to be applied to a file.
pub struct FilterList<'repo> {
    raw: *mut raw::git_filter_list,
    _marker: marker::PhantomData<&'repo Repository>,
}

impl<'repo> FilterList<'repo> {
    /// Load the filter list for a given path.
    ///
    /// This will return `Ok(None)` if no filters are needed for the given file.
    ///
    /// # Example
    /// ```no_run
    /// use git2::{Repository, FilterList, FilterMode, FilterFlags};
    ///
    /// let repo = Repository::open(".").unwrap();
    /// let filters = FilterList::load(&repo, "path/to/file.txt", FilterMode::ToOdb, FilterFlags::DEFAULT);
    /// ```
    pub fn load(
        repo: &'repo Repository,
        path: &str,
        mode: FilterMode,
        flags: FilterFlags,
    ) -> Result<Option<FilterList<'repo>>, Error> {
        Self::load_with_blob(repo, None, path, mode, flags)
    }

    /// Load the filter list for a given path with an optional blob.
    ///
    /// The blob can be used to provide additional context about the file
    /// being filtered.
    pub fn load_with_blob(
        repo: &'repo Repository,
        blob: Option<&Blob<'_>>,
        path: &str,
        mode: FilterMode,
        flags: FilterFlags,
    ) -> Result<Option<FilterList<'repo>>, Error> {
        let path = CString::new(path)?;
        let mut raw = ptr::null_mut();
        let blob_ptr = blob.map(|b| b.raw()).unwrap_or(ptr::null_mut());

        unsafe {
            let rc = raw::git_filter_list_load(
                &mut raw,
                repo.raw(),
                blob_ptr,
                path.as_ptr(),
                mode.raw(),
                flags.bits(),
            );
            if rc < 0 {
                return Err(Error::last_error(rc));
            }
        }

        if raw.is_null() {
            Ok(None)
        } else {
            Ok(Some(FilterList {
                raw,
                _marker: marker::PhantomData,
            }))
        }
    }

    /// Check if a named filter will be applied.
    ///
    /// The built-in filters "crlf" and "ident" can be queried, as well as
    /// any custom filters that have been registered.
    pub fn contains(&self, name: &str) -> bool {
        let name = match CString::new(name) {
            Ok(n) => n,
            Err(_) => return false,
        };
        unsafe { raw::git_filter_list_contains(self.raw, name.as_ptr()) != 0 }
    }

    /// Apply the filter list to a data buffer.
    ///
    /// Returns the filtered data.
    pub fn apply_to_buffer(&self, data: &[u8]) -> Result<Buf, Error> {
        let buf = Buf::new();
        unsafe {
            let rc = raw::git_filter_list_apply_to_buffer(
                buf.raw(),
                self.raw,
                data.as_ptr() as *const _,
                data.len(),
            );
            if rc < 0 {
                return Err(Error::last_error(rc));
            }
        }
        Ok(buf)
    }

    /// Apply the filter list to a file on disk.
    ///
    /// The path should be relative to the repository root.
    pub fn apply_to_file(&self, repo: &Repository, path: &str) -> Result<Buf, Error> {
        let path = CString::new(path)?;
        let buf = Buf::new();
        unsafe {
            let rc = raw::git_filter_list_apply_to_file(
                buf.raw(),
                self.raw,
                repo.raw(),
                path.as_ptr(),
            );
            if rc < 0 {
                return Err(Error::last_error(rc));
            }
        }
        Ok(buf)
    }

    /// Apply the filter list to a blob.
    pub fn apply_to_blob(&self, blob: &Blob<'_>) -> Result<Buf, Error> {
        let buf = Buf::new();
        unsafe {
            let rc = raw::git_filter_list_apply_to_blob(buf.raw(), self.raw, blob.raw());
            if rc < 0 {
                return Err(Error::last_error(rc));
            }
        }
        Ok(buf)
    }

    /// Get the number of filters in this list.
    pub fn len(&self) -> usize {
        unsafe { raw::git_filter_list_length(self.raw) }
    }

    /// Check if the filter list is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'repo> Drop for FilterList<'repo> {
    fn drop(&mut self) {
        unsafe { raw::git_filter_list_free(self.raw) }
    }
}

// ============================================================================
// Filter Registration API
// ============================================================================

use std::ffi::CStr;
use std::os::raw::c_void;
use std::sync::Mutex;

/// Information about the file being filtered.
///
/// This provides context to filter implementations about the source file.
pub struct FilterSource<'a> {
    raw: *const raw::git_filter_source,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a> FilterSource<'a> {
    fn from_raw(raw: *const raw::git_filter_source) -> Self {
        FilterSource {
            raw,
            _marker: marker::PhantomData,
        }
    }

    /// Get the path of the file being filtered, relative to the repository.
    pub fn path(&self) -> Option<&str> {
        unsafe {
            let ptr = raw::git_filter_source_path(self.raw);
            if ptr.is_null() {
                None
            } else {
                CStr::from_ptr(ptr).to_str().ok()
            }
        }
    }

    /// Get the file mode of the source file.
    pub fn filemode(&self) -> u16 {
        unsafe { raw::git_filter_source_filemode(self.raw) }
    }

    /// Get the direction of filtering (to worktree or to odb).
    pub fn mode(&self) -> FilterMode {
        unsafe {
            match raw::git_filter_source_mode(self.raw) {
                raw::GIT_FILTER_TO_WORKTREE => FilterMode::ToWorktree,
                raw::GIT_FILTER_TO_ODB => FilterMode::ToOdb,
                _ => FilterMode::ToWorktree,
            }
        }
    }
}

/// Result of the filter check callback.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FilterCheck {
    /// Apply this filter to the file.
    Apply,
    /// Skip this filter (passthrough).
    Skip,
}

/// Trait for implementing custom Git filters.
///
/// Implement this trait to create filters that transform file content
/// during checkout (smudge) and commit (clean) operations.
///
/// # Example
///
/// ```ignore
/// use git2::{Filter, FilterSource, FilterMode, FilterCheck};
///
/// struct UppercaseFilter;
///
/// impl Filter for UppercaseFilter {
///     fn check(&self, src: &FilterSource) -> Result<FilterCheck, git2::Error> {
///         // Only apply to .txt files
///         match src.path() {
///             Some(p) if p.ends_with(".txt") => Ok(FilterCheck::Apply),
///             _ => Ok(FilterCheck::Skip),
///         }
///     }
///
///     fn apply(&self, src: &FilterSource, input: &[u8]) -> Result<Vec<u8>, git2::Error> {
///         match src.mode() {
///             FilterMode::ToWorktree => Ok(input.to_ascii_uppercase()),
///             FilterMode::ToOdb => Ok(input.to_ascii_lowercase()),
///         }
///     }
/// }
/// ```
pub trait Filter: Send + Sync {
    /// Check if this filter should be applied to the given file.
    ///
    /// Return `FilterCheck::Apply` to run the filter, or `FilterCheck::Skip` to pass through.
    /// The default implementation always applies the filter.
    fn check(&self, _src: &FilterSource<'_>) -> Result<FilterCheck, Error> {
        Ok(FilterCheck::Apply)
    }

    /// Apply the filter to transform the content.
    ///
    /// - For `FilterMode::ToWorktree` (smudge): transform from repository to working directory
    /// - For `FilterMode::ToOdb` (clean): transform from working directory to repository
    fn apply(&self, src: &FilterSource<'_>, input: &[u8]) -> Result<Vec<u8>, Error>;

    /// Called when the filter is being shut down.
    ///
    /// Override this to clean up resources. Default does nothing.
    fn shutdown(&self) {}
}

/// Priority levels for filter registration.
pub mod filter_priority {
    /// Priority for CRLF filter (0).
    pub const CRLF: i32 = 0;
    /// Priority for ident filter (100).
    pub const IDENT: i32 = 100;
    /// Priority for driver/custom filters (200). Use this for LFS.
    pub const DRIVER: i32 = 200;
}

/// A handle to a registered filter.
///
/// When dropped, the filter is unregistered.
pub struct FilterRegistration {
    name: CString,
    // Prevent Send/Sync - must be dropped on same thread
    _marker: marker::PhantomData<*mut ()>,
}

impl Drop for FilterRegistration {
    fn drop(&mut self) {
        unsafe {
            // Ignore errors during unregistration
            let _ = raw::git_filter_unregister(self.name.as_ptr());
        }

        // Clean up from registry
        let mut registry = get_registry().lock().unwrap();
        registry.retain(|entry| entry.name.as_c_str() != self.name.as_c_str());
    }
}

// Internal storage for registered filters
struct FilterEntry {
    name: CString,
    filter: Box<dyn Filter>,
    raw_filter: *mut raw::git_filter,
}

// Safety: FilterEntry is Send because Filter is Send + Sync
unsafe impl Send for FilterEntry {}

use std::sync::OnceLock;

static FILTER_REGISTRY: OnceLock<Mutex<Vec<FilterEntry>>> = OnceLock::new();

fn get_registry() -> &'static Mutex<Vec<FilterEntry>> {
    FILTER_REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}

/// Register a custom filter.
///
/// The filter will be applied to files matching the given attribute pattern.
/// For example, to apply to files with `filter=lfs` in `.gitattributes`, use
/// `attributes = "filter=lfs"`.
///
/// Returns a `FilterRegistration` handle. The filter remains registered until
/// this handle is dropped.
///
/// # Arguments
///
/// * `name` - Unique name for the filter (e.g., "lfs")
/// * `attributes` - Attribute pattern to match (e.g., "filter=lfs")
/// * `priority` - Filter priority (use `filter_priority::DRIVER` for custom filters)
/// * `filter` - The filter implementation
///
/// # Example
///
/// ```ignore
/// use git2::{filter_register, filter_priority, Filter, FilterSource, FilterCheck};
///
/// struct MyFilter;
/// impl Filter for MyFilter {
///     fn apply(&self, _src: &FilterSource, input: &[u8]) -> Result<Vec<u8>, git2::Error> {
///         Ok(input.to_vec())
///     }
/// }
///
/// let registration = filter_register("myfilter", "filter=myfilter", filter_priority::DRIVER, MyFilter)?;
/// // Filter is now active
/// drop(registration); // Unregisters the filter
/// ```
pub fn filter_register<F: Filter + 'static>(
    name: &str,
    attributes: &str,
    priority: i32,
    filter: F,
) -> Result<FilterRegistration, Error> {
    // Ensure libgit2 is initialized
    crate::init();

    let name_cstr = CString::new(name)?;
    let attributes_cstr = CString::new(attributes)?;

    // Box the filter
    let filter_box: Box<dyn Filter> = Box::new(filter);

    // Create the raw git_filter struct
    let raw_filter = Box::into_raw(Box::new(raw::git_filter {
        version: raw::GIT_FILTER_VERSION,
        attributes: attributes_cstr.as_ptr(),
        initialize: None,
        shutdown: Some(filter_shutdown_cb),
        check: Some(filter_check_cb),
        apply: Some(filter_apply_cb),
        stream: None, // We use apply, not stream
        cleanup: Some(filter_cleanup_cb),
    }));

    // Store the entry
    let entry = FilterEntry {
        name: name_cstr.clone(),
        filter: filter_box,
        raw_filter,
    };

    {
        let mut registry = get_registry().lock().unwrap();
        registry.push(entry);
    }

    // Register with libgit2
    unsafe {
        let rc = raw::git_filter_register(name_cstr.as_ptr(), raw_filter, priority);
        if rc < 0 {
            // Clean up on failure
            let mut registry = get_registry().lock().unwrap();
            registry.retain(|e| e.name.as_c_str() != name_cstr.as_c_str());
            let _ = Box::from_raw(raw_filter);
            return Err(Error::last_error(rc));
        }
    }

    // Leak the attributes string - it must live as long as the filter is registered
    std::mem::forget(attributes_cstr);

    Ok(FilterRegistration {
        name: name_cstr,
        _marker: marker::PhantomData,
    })
}

// Find filter by raw pointer
fn find_filter(raw: *mut raw::git_filter) -> Option<&'static dyn Filter> {
    let registry = get_registry().lock().unwrap();
    for entry in registry.iter() {
        if entry.raw_filter == raw {
            // Safety: The filter lives as long as the registry entry
            // We return a 'static reference because the filter is Box<dyn Filter>
            // stored in the registry, which lives until unregistration
            let filter_ref: &dyn Filter = &*entry.filter;
            return Some(unsafe { std::mem::transmute::<&dyn Filter, &'static dyn Filter>(filter_ref) });
        }
    }
    None
}

// C callback: shutdown
unsafe extern "C" fn filter_shutdown_cb(filter: *mut raw::git_filter) {
    if let Some(f) = find_filter(filter) {
        f.shutdown();
    }
}

// C callback: check
unsafe extern "C" fn filter_check_cb(
    filter: *mut raw::git_filter,
    _payload: *mut *mut c_void,
    src: *const raw::git_filter_source,
    _attr_values: *mut *const std::os::raw::c_char,
) -> std::os::raw::c_int {
    let Some(f) = find_filter(filter) else {
        return raw::GIT_PASSTHROUGH;
    };

    let source = FilterSource::from_raw(src);
    match f.check(&source) {
        Ok(FilterCheck::Apply) => 0,
        Ok(FilterCheck::Skip) => raw::GIT_PASSTHROUGH,
        Err(_) => -1,
    }
}

// C callback: apply
unsafe extern "C" fn filter_apply_cb(
    filter: *mut raw::git_filter,
    _payload: *mut *mut c_void,
    to: *mut raw::git_buf,
    from: *const raw::git_buf,
    src: *const raw::git_filter_source,
) -> std::os::raw::c_int {
    let Some(f) = find_filter(filter) else {
        return raw::GIT_PASSTHROUGH;
    };

    let source = FilterSource::from_raw(src);

    // Read input
    let input = if (*from).ptr.is_null() || (*from).size == 0 {
        &[]
    } else {
        std::slice::from_raw_parts((*from).ptr as *const u8, (*from).size)
    };

    // Apply filter
    match f.apply(&source, input) {
        Ok(output) => {
            // Write output to git_buf
            let rc = raw::git_buf_set(to, output.as_ptr() as *const c_void, output.len());
            if rc < 0 {
                return rc;
            }
            0
        }
        Err(_) => -1,
    }
}

// C callback: cleanup (per-file cleanup, not shutdown)
unsafe extern "C" fn filter_cleanup_cb(
    _filter: *mut raw::git_filter,
    _payload: *mut c_void,
) {
    // Nothing to clean up per-file for our implementation
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Repository;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    fn repo_init() -> (TempDir, Repository) {
        let td = TempDir::new().unwrap();
        let repo = Repository::init(td.path()).unwrap();
        {
            let mut config = repo.config().unwrap();
            config.set_str("user.name", "name").unwrap();
            config.set_str("user.email", "email").unwrap();
        }
        (td, repo)
    }

    #[test]
    fn test_filter_mode_values() {
        assert_eq!(FilterMode::ToWorktree.raw(), raw::GIT_FILTER_TO_WORKTREE);
        assert_eq!(FilterMode::ToOdb.raw(), raw::GIT_FILTER_TO_ODB);
    }

    #[test]
    fn test_filter_flags() {
        let flags = FilterFlags::DEFAULT | FilterFlags::ALLOW_UNSAFE;
        assert!(flags.contains(FilterFlags::ALLOW_UNSAFE));
        assert!(!flags.contains(FilterFlags::NO_SYSTEM_ATTRIBUTES));
    }

    #[test]
    fn test_filter_list_load_no_filters() {
        let (_td, repo) = repo_init();

        // Load filters for a path that doesn't have any filters configured
        let result = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT);
        assert!(result.is_ok());
        // No filters configured, so should return None
        let filters = result.unwrap();
        assert!(filters.is_none());
    }

    #[test]
    fn test_filter_list_with_gitattributes() {
        let (td, repo) = repo_init();

        // Create a .gitattributes file that enables text filtering
        let gitattributes_path = td.path().join(".gitattributes");
        {
            let mut file = File::create(&gitattributes_path).unwrap();
            writeln!(file, "*.txt text").unwrap();
        }

        // Add and commit the .gitattributes
        {
            let mut index = repo.index().unwrap();
            index.add_path(std::path::Path::new(".gitattributes")).unwrap();
            index.write().unwrap();
        }

        // Now load filters for a .txt file
        let result = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT);
        assert!(result.is_ok());

        // Use explicit binding to control lifetime
        let filters_opt = result.unwrap();
        if let Some(ref filters) = filters_opt {
            // Check if crlf filter is active (it should be for 'text' attribute)
            let has_crlf = filters.contains("crlf");
            // The actual presence depends on platform, just verify it doesn't crash
            let _ = has_crlf;

            // Verify len() works
            let _len = filters.len();
        }
        drop(filters_opt);
    }

    #[test]
    fn test_filter_apply_to_buffer() {
        let (td, repo) = repo_init();

        // Create .gitattributes with text attribute
        let gitattributes_path = td.path().join(".gitattributes");
        {
            let mut file = File::create(&gitattributes_path).unwrap();
            writeln!(file, "*.txt text").unwrap();
        }

        {
            let mut index = repo.index().unwrap();
            index.add_path(std::path::Path::new(".gitattributes")).unwrap();
            index.write().unwrap();
        }

        // Try to apply filters to a buffer
        let filters_opt = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT).unwrap();
        if let Some(ref filters) = filters_opt {
            let input = b"Hello\r\nWorld\r\n";
            let result = filters.apply_to_buffer(input);
            assert!(result.is_ok());
            // The buffer should be processed (possibly CRLF -> LF on some platforms)
            let _output = result.unwrap();
        }
        drop(filters_opt);
    }

    #[test]
    fn test_filter_apply_to_file() {
        let (td, repo) = repo_init();

        // Create .gitattributes
        let gitattributes_path = td.path().join(".gitattributes");
        {
            let mut file = File::create(&gitattributes_path).unwrap();
            writeln!(file, "*.txt text").unwrap();
        }

        // Create a test file
        let test_file_path = td.path().join("test.txt");
        {
            let mut file = File::create(&test_file_path).unwrap();
            writeln!(file, "Hello World").unwrap();
        }

        {
            let mut index = repo.index().unwrap();
            index.add_path(std::path::Path::new(".gitattributes")).unwrap();
            index.add_path(std::path::Path::new("test.txt")).unwrap();
            index.write().unwrap();
        }

        // Apply filters to the file
        let filters_opt = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT).unwrap();
        if let Some(ref filters) = filters_opt {
            let result = filters.apply_to_file(&repo, "test.txt");
            assert!(result.is_ok());
        }
        drop(filters_opt);
    }

    #[test]
    fn test_filter_list_contains() {
        let (td, repo) = repo_init();

        // Create .gitattributes with text and ident
        let gitattributes_path = td.path().join(".gitattributes");
        {
            let mut file = File::create(&gitattributes_path).unwrap();
            writeln!(file, "*.txt text ident").unwrap();
        }

        {
            let mut index = repo.index().unwrap();
            index.add_path(std::path::Path::new(".gitattributes")).unwrap();
            index.write().unwrap();
        }

        let filters_opt = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT).unwrap();
        if let Some(ref filters) = filters_opt {
            // Should have both crlf and ident filters
            // Note: actual presence depends on gitattributes processing
            let _ = filters.contains("crlf");
            let _ = filters.contains("ident");
            let _ = filters.contains("nonexistent");
        }
        drop(filters_opt);
    }

    #[test]
    fn test_filter_list_empty() {
        let (_td, repo) = repo_init();

        // No gitattributes, so filters should be None or empty
        let result = FilterList::load(&repo, "test.txt", FilterMode::ToOdb, FilterFlags::DEFAULT);
        assert!(result.is_ok());

        let filters_opt = result.unwrap();
        match filters_opt {
            Some(ref filters) => assert!(filters.is_empty()),
            None => {} // This is also valid
        }
        drop(filters_opt);
    }

    // ========================================================================
    // Custom Filter Registration Tests
    // ========================================================================

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    // Counter for generating unique filter names across tests
    static TEST_FILTER_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn unique_filter_name(prefix: &str) -> String {
        let id = TEST_FILTER_COUNTER.fetch_add(1, Ordering::SeqCst);
        format!("{}_{}", prefix, id)
    }

    /// A simple test filter that uppercases on clean, lowercases on smudge
    struct CaseFilter {
        apply_count: Arc<AtomicUsize>,
    }

    impl Filter for CaseFilter {
        fn apply(&self, src: &FilterSource<'_>, input: &[u8]) -> Result<Vec<u8>, Error> {
            self.apply_count.fetch_add(1, Ordering::SeqCst);
            match src.mode() {
                FilterMode::ToOdb => {
                    // Clean: uppercase
                    Ok(input.to_ascii_uppercase())
                }
                FilterMode::ToWorktree => {
                    // Smudge: lowercase
                    Ok(input.to_ascii_lowercase())
                }
            }
        }
    }

    #[test]
    fn test_custom_filter_registration() {
        let apply_count = Arc::new(AtomicUsize::new(0));
        let filter = CaseFilter {
            apply_count: apply_count.clone(),
        };

        let name = unique_filter_name("casefilter");
        let attr = format!("filter={}", name);

        // Register the filter
        let registration = filter_register(&name, &attr, filter_priority::DRIVER, filter);
        assert!(registration.is_ok(), "Failed to register filter: {:?}", registration.err());
        let _reg = registration.unwrap();

        // Filter is now registered - verify it exists in registry
        let registry = get_registry().lock().unwrap();
        assert!(registry.iter().any(|e| e.name.to_str().unwrap() == name));
        drop(registry);

        // When _reg is dropped, the filter will be unregistered
    }

    #[test]
    fn test_custom_filter_with_gitattributes() {
        let (td, repo) = repo_init();

        let apply_count = Arc::new(AtomicUsize::new(0));
        let filter = CaseFilter {
            apply_count: apply_count.clone(),
        };

        let name = unique_filter_name("testcase");
        let attr = format!("filter={}", name);

        // Register the filter with a unique name for this test
        let registration = filter_register(&name, &attr, filter_priority::DRIVER, filter)
            .expect("Failed to register filter");

        // Create .gitattributes to use our filter
        let gitattributes_path = td.path().join(".gitattributes");
        {
            let mut file = File::create(&gitattributes_path).unwrap();
            writeln!(file, "*.upper filter={}", name).unwrap();
        }

        // Add gitattributes to index
        {
            let mut index = repo.index().unwrap();
            index
                .add_path(std::path::Path::new(".gitattributes"))
                .unwrap();
            index.write().unwrap();
        }

        // Load filters for a .upper file
        let filters = FilterList::load(
            &repo,
            "test.upper",
            FilterMode::ToOdb,
            FilterFlags::DEFAULT,
        )
        .unwrap();

        // Should have our custom filter
        if let Some(ref f) = filters {
            assert!(f.contains(&name));

            // Apply the filter
            let input = b"hello world";
            let output = f.apply_to_buffer(input).unwrap();
            assert_eq!(output.as_ref(), b"HELLO WORLD");
            assert_eq!(apply_count.load(Ordering::SeqCst), 1);
        } else {
            panic!("Expected filter list to be Some");
        }

        drop(filters);
        drop(registration);
    }

    #[test]
    fn test_filter_unregistration() {
        let filter = CaseFilter {
            apply_count: Arc::new(AtomicUsize::new(0)),
        };

        let name = unique_filter_name("tempfilter");
        let attr = format!("filter={}", name);

        // Register
        let registration = filter_register(&name, &attr, filter_priority::DRIVER, filter)
            .expect("Failed to register filter");

        // Verify registered
        {
            let registry = get_registry().lock().unwrap();
            assert!(registry.iter().any(|e| e.name.to_str().unwrap() == name));
        }

        // Drop to unregister
        drop(registration);

        // Verify unregistered
        {
            let registry = get_registry().lock().unwrap();
            assert!(!registry.iter().any(|e| e.name.to_str().unwrap() == name));
        }
    }
}
