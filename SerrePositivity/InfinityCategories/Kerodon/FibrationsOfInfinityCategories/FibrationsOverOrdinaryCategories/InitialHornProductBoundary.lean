module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornProductExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：外側ホーン上の図式と標準単体の境界上の族の可逆な辺による貼り合わせ。
方針：積の和の pushout で二つの射を貼って正則 pairing の延長を使う。
規約：標準単体の最初の頂点上の辺だけに可逆性を仮定する。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の制限のホーンの相対充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：最初の外側ホーン上の図式と境界上の族は指定辺が可逆なら同時に延長できる。
方針：pushout で貼って積の外側ホーンの pairing の充填を適用し、両制限を回収する。
規約：X は quasicategory、右因子の次元は任意。
使われ方：Kerodon §5.3.7（Tag 01US） の相対骨格の一つのセルの充填。 -/
lemma initialHornProduct_fill_boundary {X : SSet.{u}} [Quasicategory X] (m n : ℕ)
    (G : (Δ[m + 2] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ X)
    (H : (horn (m + 2) 0 : SSet.{u}) ⊗ Δ[n] ⟶ X)
    (hw : ((horn (m + 2) 0).ι ▷ (boundary n : SSet.{u})) ≫ G =
      ((horn (m + 2) 0 : SSet.{u}) ◁ (boundary n).ι) ≫ H)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) 1)))) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⊗ Δ[n] ⟶ X,
      (Δ[m + 2] ◁ (boundary n).ι) ≫ F = G ∧ ((horn (m + 2) 0).ι ▷ Δ[n]) ≫ F = H := by
  let S := horn.{u} (m + 2) 0
  let T := boundary.{u} n
  let q := Subcomplex.unionProd.isPushout S T
  let a := q.desc G H hw
  have hG : Subcomplex.unionProd.ι₁ S T ≫ a = G := q.inl_desc _ _ _
  have hH : Subcomplex.unionProd.ι₂ S T ≫ a = H := q.inr_desc _ _ _
  have he : a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge m n, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge_mem m n⟩ =
      H.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) 1) := by
    let v : ((horn (m + 2) 0 : SSet.{u}) ⊗ Δ[n]) _⦋1⦌ :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) 1⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hH (Opposite.op ⦋1⦌)) v
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProduct_exists_extension_of_invertible_firstEdge m n a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 hi)
  refine ⟨F, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, hG]
  · rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, hH]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
