module
public import Mathlib.CategoryTheory.Monoidal.Category
/-!
概要：Hom 対象の等式と単位・合成の異種等式に沿って豊穣圏の三法則を移す。
方針：抽象 Hom 対象上で等式を消去し、実際の提示複体の展開を避ける。
規約：追加の圏法則や公理は仮定せず、元の三法則を入力として移送する。
使われ方：非連結和の提示 Hom の条件分岐を、小さい kernel 項で検証する。
-/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category V] [MonoidalCategory V]

lemma enrichedLeftLaw_of_heq {U H U' H' : V} (hU : U = U') (hH : H = H')
    (i : 𝟙_ V ⟶ U) (i' : 𝟙_ V ⟶ U') (c : U ⊗ H ⟶ H) (c' : U' ⊗ H' ⟶ H')
    (hi : HEq i i') (hc : HEq c c')
    (h : (λ_ H').inv ≫ i' ▷ H' ≫ c' = 𝟙 H') :
    (λ_ H).inv ≫ i ▷ H ≫ c = 𝟙 H := by
  cases hU
  cases hH
  cases hi
  cases hc
  exact h

lemma enrichedRightLaw_of_heq {U H U' H' : V} (hU : U = U') (hH : H = H')
    (i : 𝟙_ V ⟶ U) (i' : 𝟙_ V ⟶ U') (c : H ⊗ U ⟶ H) (c' : H' ⊗ U' ⟶ H')
    (hi : HEq i i') (hc : HEq c c')
    (h : (ρ_ H').inv ≫ H' ◁ i' ≫ c' = 𝟙 H') :
    (ρ_ H).inv ≫ H ◁ i ≫ c = 𝟙 H := by
  cases hU
  cases hH
  cases hi
  cases hc
  exact h

lemma enrichedAssocLaw_of_heq {A B C D E F A' B' C' D' E' F' : V}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D') (hE : E = E') (hF : F = F')
    (p : A ⊗ B ⟶ D) (q : D ⊗ C ⟶ F) (r : B ⊗ C ⟶ E) (s : A ⊗ E ⟶ F)
    (p' : A' ⊗ B' ⟶ D') (q' : D' ⊗ C' ⟶ F') (r' : B' ⊗ C' ⟶ E') (s' : A' ⊗ E' ⟶ F')
    (hp : HEq p p') (hq : HEq q q') (hr : HEq r r') (hs : HEq s s')
    (h : (α_ A' B' C').inv ≫ p' ▷ C' ≫ q' = A' ◁ r' ≫ s') :
    (α_ A B C).inv ≫ p ▷ C ≫ q = A ◁ r ≫ s := by
  cases hA
  cases hB
  cases hC
  cases hD
  cases hE
  cases hF
  cases hp
  cases hq
  cases hr
  cases hs
  exact h

lemma enrichedFunctorUnitLaw_of_heq {A B A' B' : V} (hA : A = A') (hB : B = B')
    (i : 𝟙_ V ⟶ A) (j : 𝟙_ V ⟶ B) (f : A ⟶ B)
    (i' : 𝟙_ V ⟶ A') (j' : 𝟙_ V ⟶ B') (f' : A' ⟶ B')
    (hi : HEq i i') (hj : HEq j j') (hf : HEq f f') (h : i' ≫ f' = j') :
    i ≫ f = j := by
  cases hA
  cases hB
  cases hi
  cases hj
  cases hf
  exact h

lemma enrichedFunctorCompLaw_of_heq {A B C U V' W A' B' C' U' V'' W' : V}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (hU : U = U') (hV : V' = V'') (hW : W = W')
    (p : A ⊗ B ⟶ C) (q : U ⊗ V' ⟶ W) (f : A ⟶ U) (g : B ⟶ V') (k : C ⟶ W)
    (p' : A' ⊗ B' ⟶ C') (q' : U' ⊗ V'' ⟶ W')
    (f' : A' ⟶ U') (g' : B' ⟶ V'') (k' : C' ⟶ W')
    (hp : HEq p p') (hq : HEq q q') (hf : HEq f f')
    (hg : HEq g g') (hk : HEq k k') (h : p' ≫ k' = (f' ⊗ₘ g') ≫ q') :
    p ≫ k = (f ⊗ₘ g) ≫ q := by
  cases hA
  cases hB
  cases hC
  cases hU
  cases hV
  cases hW
  cases hp
  cases hq
  cases hf
  cases hg
  cases hk
  exact h

end SerrePositivity.DifferentialGraded
