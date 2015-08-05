@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN TREAP ======================
%r% %test_dir%\treap\treap-insert-rec.c ^
    %test_dir%\treap\treap-find-rec.c ^
    %test_dir%\treap\treap-delete-rec.c ^
    %test_dir%\treap\treap-remove-root-rec.c ^
    | findstr "Verification function error"
echo ======================  END TREAP ======================
