echo off
echo ====================== BEGIN SLL ======================
vcc /smoke sll-insert.c ^
    sll-delete-all.c ^
    sll-reverse.c ^
    sll-find.c ^
    sll-insert-front.c ^
    sll-insert-back.c ^
    sll-copy-all.c ^
    sll-append.c ^
    | grep sll
::    /pipe:dump+after+dryad-end > sll_dump_after_dryad_end
echo ======================  END SLL ======================
