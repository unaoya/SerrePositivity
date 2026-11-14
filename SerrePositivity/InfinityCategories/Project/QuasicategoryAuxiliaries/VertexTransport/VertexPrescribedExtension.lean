module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.ZeroBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! # 頂点の像を指定した相対延長
概要：部分図式と全頂点の像を固定した上で図式を延長する。
方針：離散的な全頂点を部分図式に貼り、混合端点充填を使う。
規約：頂点での指定は既存部分と一致する。使われ方：零対角の零次元の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory Limits SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：部分図式と全頂点の像を保った相対延長が存在する。
方針：頂点の定値単体の部分複体と貼り合わせ、新しい単体の普遍的な端点で充填する。
規約：標的の quasicategory 性は不要。使われ方：第一行への零対角の追加。 -/
lemma exists_extension_with_vertices {B X : SSet.{u}} (A : B.Subcomplex)
    (a : (A : SSet.{u}) ⟶ X) (x : B _⦋0⦌ → X _⦋0⦌)
    (hx : ∀ v : (A : SSet.{u}) _⦋0⦌, x v.val = a.app (Opposite.op ⦋0⦌) v)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s)) ∨ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s))) :
    ∃ F : B ⟶ X, A.ι ≫ F = a ∧ ∀ v, F.app (Opposite.op ⦋0⦌) v = x v := by
  classical
  let V := Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι B)
  let e := asIso (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι B))
  let fV : (V : SSet.{u}) ⟶ X := e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x
  have hfV : Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι B) ≫ fV = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x := by
    change e.hom ≫ e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x
    rw [Iso.hom_inv_id_assoc]
  let q : IsPushout (Subcomplex.homOfLE (inf_le_left : A ⊓ V ≤ A))
      (Subcomplex.homOfLE (inf_le_right : A ⊓ V ≤ V))
      (Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ V))
      (Subcomplex.homOfLE (le_sup_right : V ≤ A ⊔ V)) :=
    (show Subcomplex.BicartSq (A ⊓ V) A V (A ⊔ V) from ⟨rfl, rfl⟩).isPushout
  have hw : Subcomplex.homOfLE (inf_le_left : A ⊓ V ≤ A) ≫ a =
      Subcomplex.homOfLE (inf_le_right : A ⊓ V ≤ V) ≫ fV := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨v, hv⟩ := s.property.2
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n = s.val at hv
    have hm : v ∈ A.obj (Opposite.op ⦋0⦌) := by
      have hh := A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s.property.1
      change B.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s.val ∈ A.obj _ at hh
      rw [← hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hh
      exact hh
    let w : (A : SSet.{u}) _⦋0⦌ := ⟨v, hm⟩
    have ha : a.app (Opposite.op ⦋n⦌) ⟨s.val, s.property.1⟩ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) n := by
      have hs : (⟨s.val, s.property.1⟩ : (A : SSet.{u}) _⦋n⦌) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant w n := by
        apply Subtype.ext
        exact hv.symm
      rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, ← hx w]
    have hb := ConcreteCategory.congr_hom (NatTrans.congr_app hfV (Opposite.op ⦋n⦌)) v
    change fV.app (Opposite.op ⦋n⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n, _⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) n at hb
    change a.app (Opposite.op ⦋n⦌) ⟨s.val, _⟩ = fV.app (Opposite.op ⦋n⦌) ⟨s.val, _⟩
    rw [ha]
    have hvv : (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n, by exact ⟨v, rfl⟩⟩ : (V : SSet.{u}) _⦋n⦌) =
        ⟨s.val, s.property.2⟩ := Subtype.ext hv
    rw [hvv] at hb
    exact hb.symm
  let g := q.desc a fV hw
  have hgA : Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ V) ≫ g = a := q.inl_desc _ _ _
  have hgV : Subcomplex.homOfLE (le_sup_right : V ≤ A ⊔ V) ≫ g = fV := q.inr_desc _ _ _
  have hAV : ∀ v : B _⦋0⦌, v ∈ (A ⊔ V).obj (Opposite.op ⦋0⦌) := by
    intro v
    right
    exact ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero v⟩
  have hgv (v : B _⦋0⦌) : g.app (Opposite.op ⦋0⦌) ⟨v, hAV v⟩ = x v := by
    have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
      (show Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι B) ≫
        Subcomplex.homOfLE (le_sup_right : V ≤ A ⊔ V) ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x by
          rw [hgV, hfV])
    change g.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0, _⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) 0 at hh
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hh
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_of_initial_or_terminal_endpoints (A ⊔ V) hAV g (by
    intro n s hs
    have hsa : s ∉ A.obj (Opposite.op ⦋n + 1⦌) := fun h ↦ hs (Or.inl h)
    rw [hgv, hgv]
    exact ht n s hsa)
  refine ⟨F, ?_, ?_⟩
  · have hh := congrArg (fun f ↦ Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ V) ≫ f) hF
    simpa only [← Category.assoc, Subcomplex.homOfLE_ι, hgA] using hh
  · intro v
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) ⟨v, hAV v⟩
    exact hh.trans (hgv v)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
