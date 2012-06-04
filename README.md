# Agda Prelude

The Prelude module wraps and exports common functionality from the Agda
standard library. It can be used as a drop-in one-line import statement
to access many useful modules without having to resolve name clashes
manually.

## Usage

All the modules were originally designed to be part of the Agda standard
library (thus the standard library headers), therefore they depend on the
standard library.

## Examples

The Examples directory contains 2 programs that demonstrate the usage of
the Prelude. PrefixCalculator.agda implements a simple command-line
calculator that uses Lisp-like prefix notation. TabsToSpaces.agda reads
a file and converts all tabs to the specified number of spaces.

## License

Copyright (C) 2012 Frederic Kettelhoit

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
