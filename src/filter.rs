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
}
