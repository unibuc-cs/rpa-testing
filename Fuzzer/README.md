Notes:

Problems with graphviz on Windows:
 - Best solution is to install the graphviz binaries and sources then build the pygraphfiz from source code for python: 
 
 https://github.com/pygraphviz/pygraphviz/blob/main/INSTALL.txt
 
 In the case that link dissapears:
 
 1. Download and install 2.46.0 for Windows 10 (64-bit):
   `stable_windows_10_cmake_Release_x64_graphviz-install-2.46.0-win64.exe
   <https://gitlab.com/graphviz/graphviz/-/package_files/6164164/download>`_.
2. Install PyGraphviz via

.. code-block:: console

    PS C:\> python -m pip install --global-option=build_ext `
                  --global-option="-IC:\Program Files\Graphviz\include" `
                  --global-option="-LC:\Program Files\Graphviz\lib" `
                  pygraphviz



