Compiling
=========

1. You need a C/C++ compiler, Flex and Bison, and GNU make.
   The GNU Make needs to be version 3.81 or higher.
   On Debian-like distributions, including Ubuntu, do as root:
   ```
   apt-get install g++ gcc flex bison make git curl patch
   ```
   On Red Hat/Fedora or derivates, do as root:
   ```
   dnf install gcc gcc-c++ flex bison curl patch
   ```
   Note that you need g++ version 7.0 or newer.

   On Amazon Linux and similar distributions, do as root:
   ```
   yum install gcc72-c++ flex bison curl patch tar
   ```

2. Initialize and update the CBMC submodule:
   ```
   git submodule init; git submodule update
   ```

3. Download minisat:
   ```
   make -C lib/cbmc/src minisat2-download
   ```

4. Build EBMC:
   ```
   make -C src
   ```
   This also builds the CBMC submodule. The binary will be in src/ebmc/ebmc.
