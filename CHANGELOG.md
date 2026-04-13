Changelog
=========

0.1.11
------

* Fixed behavior of `BytesDecoder::fold` so it matches `BytesDecoder::next`.
  Now, when `DecodeBytesError::InvalidUtf8` and `DecodeBytesError::DecodeError`
  are produced at the same time, only `InvalidUtf8` is yielded.
* Non-UTF-8 filenames are now allowed in the CLI. Any non-UTF-8 argument is
  treated as a positional argument.
* Removed erroneous implementation of `FusedIterator` on an internal type. This
  does not appear to have been used in practice.
* Added the [Eips Exceptions](licenses/Eips-Exceptions) to Base116's
  license.[^1] These exceptions retroactively apply to all previous versions of
  Base116.

[^1]: Note from taylor.fish: Base116 contains one commit that was not authored
by me. The commit consists of changing one instance of `std` to `core` in order
to fix a compilation error. While I am appreciative of the fix, I do not
believe this change meets the threshold of originality under United States
copyright law; therefore, I believe I have the ability to add exceptions to
Base116's license.

0.1.10
------

* Fixed erroneous use of `std` instead of `core`. This fixes builds when `std`
  is disabled and `alloc` is enabled. Thanks to [@tshakah] for the fix.

[@tshakah]: https://github.com/tshakah

0.1.9
-----

* Adjusted formatting of CLI help message.

0.1.8
-----

* Added documentation to previously undocumented enum variants, types, and
  modules.

0.1.7
-----

* Added MSRV to Cargo.toml.
* Removed unnecessary build script.

0.1.6
-----

* Clarified wording in README.

0.1.5
-----

* Fixed regression in version 0.1.4 where no error was generated if too many
  command-line arguments were provided.

0.1.4
-----

* Modified command-line argument processing. This change makes it impossible to
  pass non-UTF-8 filenames; this was later fixed in version 0.1.11.

0.1.3
-----

* Improved error message when an invalid character is encountered.
* `BytesDecoder::fold` now yields `DecodeBytesError::InvalidUtf8` before
  `DecodeBytesError::DecodeError` when both are produced at the same time.
  Previously, it yielded them in the opposite order. However, note that neither
  order matches the behavior of `BytesDecoder::next`. This was later fixed in
  version 0.1.11.

0.1.2
-----

* Fixed documentation for `DecodeConfig`.

0.1.1
-----

* Fixed metadata in Cargo.toml.

0.1.0
-----

Initial release.
