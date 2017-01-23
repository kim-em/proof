# Getting started with Homotopy Type Theory on the computer #

Homotopy type theory (HoTT) is intended as an alternative `foundation' for
mathematics. It can be used informally, and the HoTT book describes what this
means and how it is done. It can also be used formally, in the sense that one
can write proofs, using the language of HoTT, that computers can
automatically verify.

Although really convincing tools don't exist yet, good computer verification
is a stepping-stone to automatic tools that help us write and discover proofs.
This is what I really care about!

This note assumes you plan to learn some HoTT, and to write HoTT proofs in a
computer verifiable form.

There are three main options: Agda, Coq, and Lean. I have no experience so far
with Agda, so this note doesn't address it. Most of the work in formal HoTT
development so far has been done in Coq, and so it may be the obvious choice.
Lean is the newest option, and although it hasn't been used extensively for
HoTT at this point, it is possible and promising. (Lean, as a programming
language and proof system, has many appealing features.)

## Coq ##

... TODO ...

## Lean ##

You can run Lean directly in a web browser, or install it locally.
A local installation is eventually necessary; although the browser version is
very convenient for trying out small snippets, you'll also want to be able to
save and publish source files.

Unfortunately at this moment the active development branch of Lean does not
support HoTT, and if you want to do work in HoTT you'll need to use a
snapshot. This situation will hopefully be rectified!

The HoTT snapshot is available from https://github.com/leanprover/lean2. The
tutorial is at https://leanprover.github.io/tutorial/, and browser version is
at https://leanprover.github.io/tutorial/?live.

The active development version is at https://github.com/leanprover/lean. It
has tutorials

* [Introduction to Lean](https://leanprover.github.io/introduction_to_lean/)
* [Theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)
* [Programming in Lean](https://leanprover.github.io/programming_in_lean/)

You can access a browser version at
https://leanprover.github.io/programming_in_lean/?live.

### Installing Lean locally ###

You'll need to
* download the source code
* compile the system
* set up Visual Studio Code or emacs

#### Downloading the Lean source code ####
Make sure you've got a copy of `git` installed. On most systems this is
already available; there is also a nice graphical frontend available, called 
[SourceTree](https://www.sourcetreeapp.com/).

If you've already got a github account, and know about using git over ssh, use
the `git` URLs below. Otherwise, use the `https` URLs.

At the command line, run `git clone URL`, where URL is one of

* https://github.com/leanprover/lean.git
* git@github.com:leanprover/lean.git

(for the development branch, which doesn't support HoTT)

* https://github.com/leanprover/lean2.git
* git@github.com:leanprover/lean2.git

(for the HoTT snapshot).

This will create a subdirectory `lean` or `lean2` wherever you run the
command. It's fine to put this wherever you like, but you'll need to tell
Emacs the path later.

#### Compiling Lean ####
Compiling Lean has some prerequisites. If you are on OS X, I would recommend
installing [Macports](https://www.macports.org/install.php), and then running
the command `sudo port install cmake gmp mpfr google-perftools ninja`. If you
are on Windows, follow the instructions at
https://github.com/leanprover/lean/blob/master/doc/make/msys2.md. If you're on
Linux, you enjoy this sort of thing, don't you?

When you're ready to compile go into the `lean` or `lean2` directory, and run
the commands

    mkdir -p build/debug
    cd build/debug
    cmake -DCMAKE_BUILD_TYPE=DEBUG -DTCMALLOC=OFF -G Ninja ../../src
    ninja

(The `-DTCMALLOC=OFF` is only necessarily until `google-perftools` delivers a
bug fix on macOS Sierra.)

#### Setting up Visual Studio Code ####
(This is now my preferred solution, but if you are already an emacs user, see below.)

Install [Visual Studio Code](https://code.visualstudio.com/download), run it,
and install the lean extension by clicking the 'Extensions' button (it's the
last one in the strip of icons on the left), and searching for `lean`. You'll
likely need to go to 'Preferences' --> 'User Settings' and set the path of
your Lean binary to match wherever you installed it above.

You may also want to tell your operating system to open all `.lean` files with
Visual Studio Code. (On a mac: Select a `.lean` file in Finder, hit
<kbd>⌘</kbd><kbd>I</kbd>, select Visual Studio Code in the 'Open With' section, then
click 'Change All...'.)


#### Setting up the Lean Emacs mode ####
You'll need Emacs, at least version 24.

On OS X, I'd recommend using the 
[Emacs Mac Port](https://github.com/railwaycat/homebrew-emacsmacport), and in
particular just downloading the [pre-compiled binary]
(https://github.com/railwaycat/homebrew-emacsmacport/releases). You might also
try [Aquamacs](http://aquamacs.org/). I'd recommend telling OS X to open all
`.lean` and `.hlean` files in your preferred Emacs.

I don't know much about your Emacs options on Windows.

You'll need to add the following code to your `~/.emacs.d/init.el` file 
(create it if it doesn't already exist):

    ;; You need to modify the following two lines:
    (setq lean-rootdir "~/bin/lean")
    (setq lean-emacs-path "~/bin/lean/src/emacs")
    
    (setq lean-mode-required-packages '(company dash dash-functional f
                                   flycheck let-alist s seq))
    
    (require 'package)
    (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
    (package-initialize)
    (let ((need-to-refresh t))
      (dolist (p lean-mode-required-packages)
        (when (not (package-installed-p p))
          (when need-to-refresh
            (package-refresh-contents)
            (setq need-to-refresh nil))
          (package-install p))))
    
    (setq load-path (cons lean-emacs-path load-path))
    
    (require 'lean-mode)

You'll need to modify the first two lines, replacing `~/bin/lean` with the
directory you created when you downloaded the Lean source files.

You should now be able to open a `.lean` file, and interact with the Lean
verifier; try some examples from the relevant tutorials above. Some useful
keyboard shortcuts are <kbd>C-c C-k</kbd>, which shows the keystroke needed to
input the symbol under the cursor, and <kbd>C-c C-n</kbd> which shows the next
error in a dedicated buffer.

If you run into trouble, there is a bit more information about the Lean Emacs
mode at https://github.com/leanprover/lean/blob/master/src/emacs/README.md.


