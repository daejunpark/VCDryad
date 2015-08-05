echo off
echo ====================== BEGIN GSLIST ======================
vcc /smoke g_slist_prepend.c ^
    g_slist_last.c ^
    g_slist_concat.c ^
    g_slist_append.c ^
    g_slist_insert.c ^
    g_slist_insert_before.c ^
    g_slist_remove.c ^
    g_slist_remove_all.c ^
    g_slist_remove_link.c ^
    g_slist_delete_link.c ^
    g_slist_free.c ^
    g_slist_copy.c ^
    g_slist_reverse.c ^
    g_slist_nth.c ^
    g_slist_nth_data.c ^
    g_slist_find.c ^
    g_slist_position.c ^
    g_slist_index.c ^
    g_slist_length.c ^
    g_slist_insert_sorted.c ^
    g_slist_sort_merge.c ^
    g_slist_sort_real.c ^
    | grep slist
::    /smoke
::    /pipe:dump+after+dryad-end > sll_dump_after_dryad_end
echo ======================  END GSLIST  ======================
