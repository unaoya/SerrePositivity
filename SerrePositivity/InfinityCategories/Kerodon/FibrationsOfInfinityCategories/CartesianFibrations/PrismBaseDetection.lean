module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling

/-!
概要：標準単体の積を基底とする部分複体上の延長の可換性。
方針：標準単体の積への射を二つの射影と頂点で比較する。
規約：指定部分が全頂点を含む場合を扱う。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な prism の相対充填。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標準単体の積への射は頂点で決まる。
方針：二つの射影を標準単体への頂点による一意性で比較する。
規約：始域は任意。
使われ方：Kerodon §5.1.1（Tag 01T4） の prism の基底の確認。 -/
lemma prodStdSimplex_hom_ext_vertices {A : SSet.{u}} {m n : ℕ}
    {f g : A ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n]}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    exact congrArg (fun t ↦ t ≫ (fst (Δ[m] : SSet.{u}) Δ[n]).app (Opposite.op ⦋0⦌)) h
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    exact congrArg (fun t ↦ t ≫ (snd (Δ[m] : SSet.{u}) Δ[n]).app (Opposite.op ⦋0⦌)) h

/-- 概要：標準単体の積の全頂点を含む部分複体上で可換な延長は、中間の部分複体上でも可換。
方針：中間部分複体の頂点を元の部分に戻して二射の零次成分を比較する。
規約：E の quasicategory 性や p のファイブレーション性は不要。
使われ方：Kerodon §5.1.1（Tag 01T4） の prism のセル分解での基底の保存。 -/
lemma subcomplex_extension_over_prodStdSimplex {E : SSet.{u}} {m n : ℕ}
    (A D : ((Δ[m] : SSet.{u}) ⊗ Δ[n]).Subcomplex) (hAD : A ≤ D)
    (hA : ∀ v, v ∈ A.obj (Opposite.op ⦋0⦌))
    (p : E ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n])
    (a : (A : SSet.{u}) ⟶ E) (ha : a ≫ p = A.ι)
    (g : (D : SSet.{u}) ⟶ E) (hg : Subcomplex.homOfLE hAD ≫ g = a) :
    g ≫ p = D.ι := by
  apply prodStdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro v
  have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋0⦌))
    ⟨v.val, hA v.val⟩
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app ha (Opposite.op ⦋0⦌))
    ⟨v.val, hA v.val⟩
  exact (congrArg (p.app (Opposite.op ⦋0⦌)) hh).trans hp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
