Base116
=======

Base116 is like Base85, but it increases data size by only 1/6 instead of
1/4.

Base116 exploits properties of UTF-8 to convert arbitrary binary data to
valid, printable UTF-8, with a lower size overhead than is possible with
any printable ASCII encoding.

For example, this binary data (in hex):

```text
9329bd4b43da0bfdd1d97bdf081a2d42ec540155
```

is encoded as:

```text
Ǳ<Oȥґ|yO(WFic{2n㎨r~9*ǲ
```

Wrapping ‘Ǳ’ and ‘ǲ’ characters are added by default to make encoded data
easier to select, as the data may start or end with combining characters or
characters from right-to-left scripts.

This crate provides both a binary and a library.

Installation
------------

Install with [Cargo](https://doc.rust-lang.org/cargo/):

```bash
cargo install base116
```

Usage
-----

`base116` behaves like the `base64` binary on Unix-like systems: `base116`
encodes, and `base116 -d` decodes. See `base116 --help` for more information.

Documentation
-------------

[Documentation for the library is available on docs.rs.][docs]

[docs]: https://docs.rs/base116

License
-------

Base116 is licensed under version 3 of the GNU Affero General Public License,
or (at your option) any later version. See [LICENSE](LICENSE).

Contributing
------------

By contributing to Base116, you agree that your contribution may be used
according to the terms of Base116’s license.
