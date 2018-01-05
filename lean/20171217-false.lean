lemma main : false :=
begin
have helper : (∃ x : ℕ, true) → false :=
    λ ⟨x, h⟩, by apply _fun_match; assumption,
exact helper ⟨0, ⟨⟩⟩,
end