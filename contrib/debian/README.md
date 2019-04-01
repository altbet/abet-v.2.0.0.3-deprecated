
Debian
====================
This directory contains files used to package altbetd/altbet-qt
for Debian-based Linux systems. If you compile altbetd/altbet-qt yourself, there are some useful files here.

## altbet: URI support ##


altbet-qt.desktop  (Gnome / Open Desktop)
To install:

	sudo desktop-file-install altbet-qt.desktop
	sudo update-desktop-database

If you build yourself, you will either need to modify the paths in
the .desktop file or copy or symlink your altbetqt binary to `/usr/bin`
and the `../../share/pixmaps/altbet128.png` to `/usr/share/pixmaps`

altbet-qt.protocol (KDE)

