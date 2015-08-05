@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN MEM REGION DLL ======================
%r% %test_dir%\mem-region\mem_region_dll_ops.c ^
    | findstr "Verification fail error"
echo ======================  END MEM REGION DLL ======================
