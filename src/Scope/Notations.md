Notations used in Scope (updated on 31/03/2025)

---------------------------------------------------------------------------------------------------
symbols     input via agda          latex
≡           ==                      \equiv
◂           lb                      \blacktriangleleft
▸           lb→                     \blacktriangleright
∈           in                      \in
⊆           sub=                    \subseteq
⋈           join                    \bowtie
↦           r-|                     \mapsto
≟           ?=
---------------------------------------------------------------------------------------------------

α <> β                  α <> β                  Concatenation for Scope and Rscope
α ⊆ β                   Sub α β                 α is a sub-scope of β
[ x ]                   singleton x             Scope of one element x
x ◂                     rsingleton x            RScope of one element x
x ∈ α                   In x α                  singleton x ⊆ α
α ▸ x                   bind α x                Adds element x to Scope α
x ◂ rα                  rbind x rα              Adds element x to RScope rα
α ⋈ β ≡ γ               Split α β γ             scope γ is a mix of elements of α and β
α \[ xp ]               diffVar α xp            Scope α in which x is retired, xp : x ∈ α
p ⋈-≟ q                 decSplit p q            for p q : α ⋈ β ≡ γ, proof that p ≡ q is decidable
