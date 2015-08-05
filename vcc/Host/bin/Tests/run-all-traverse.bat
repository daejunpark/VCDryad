@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN TRAVERSE TREE ======================
%r% %test_dir%\traverse-tree\traverse-preorder.c ^
    %test_dir%\traverse-tree\traverse-posttorder.c ^
    %test_dir%\traverse-tree\traverse-inorder.c ^
    %test_dir%\traverse-tree\tree2list.c ^
    | findstr "Verification function error"
echo ======================  END TRAVERSE TREE ======================
