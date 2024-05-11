Introduction
============


What's Gnuk?
------------

Gnuk is an implementation of an USB cryptographic token for GNU Privacy
Guard.  It supports the OpenPGP card protocol version 2, and runs on
the STM32F103 processor.

This document explains Gnuk 1.2, which comes with the ECC algorithm.


Cryptographic token and feature of Gnuk
---------------------------------------

A cryptographic token is a store of private keys and it computes cryptographic
functions on the device.

The idea is to separate important secrets to an independent device, 
from where nobody can extract them.


Development Environment
-----------------------

See :doc:`development` for the development environment for Gnuk.
Gnuk is developed on an environment where there is only Free Software.


Target boards for running Gnuk
------------------------------

Hardware requirement for Gnuk is the micro controller STM32F103.
In version 1.2, Gnuk supports the following boards:

* FST-01 (Flying Stone Tiny ZERO-ONE)

* Olimex STM32-H103

* ST Nucleo F103

* Nitrokey Start


Host prerequisites for using Gnuk Token
---------------------------------------

* GNU Privacy Guard (GnuPG)

* libusb

* [Optional] SSH: openssh

* [experimental] Web: scute, firefox


Usages
------

* Sign with GnuPG
* Decrypt with GnuPG
* Use with OpenSSH through gpg-agent (as ssh-agent)
* [experimental] Use with Firefox through Scute for X.509 client certificate authentication
