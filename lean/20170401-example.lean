
namespace tree

inductive tree (α : Type ) : Type 
| node : α → list tree → tree

def at_index {a :Type} : list ℕ -> tree a -> option a
| [] (tree.node i t) := some i 
| (h::t) (tree.node i cs) := do
                                nc <- list.nth cs h ,
                                at_index t nc 

lemma helpme : forall {a} (c :a) h t tr, 
some c = at_index (h::t) tr ->
false :=
begin
intros _ _ _ _ _ sc, cases tr,
simp [at_index] at sc,
admit
end

end tree