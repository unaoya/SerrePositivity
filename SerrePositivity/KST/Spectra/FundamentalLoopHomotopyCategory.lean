module

public import SerrePositivity.KST.Spectra.FundamentalLoopEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-!
概要：元の Kan 基本群の類と、ホモトピー圏の同じ基点の自己射を全単射で結ぶ。
方針：積の充填を合成三角形へ送り、合成の等式を元の三角形へ戻して単射性を示す。
規約：積の向きは左から右。使われ方：錐の三単体の差と元の基本群の符号の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.FundamentalLoop
variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}

/-- 元の境界定数一単体の基本群の類を、同じ loop 辺のホモトピー圏の類へ送る。 -/
def toHom : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x →
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk x) :=
  Quotient.lift (fun s ↦ SSet.HomotopyCategory.homMk (edge s)) (by
    rintro s t ⟨r⟩
    have h := SSet.HomotopyCategory.homMk_comp_homMk (compStruct r)
    erw [edge_const, SSet.HomotopyCategory.homMk_id, Category.id_comp] at h
    exact h)

/-- 基本群の元の代表は、同じ元の辺の類に移る。 -/
lemma toHom_mk (s : X.PtSimplex 1 x) :
    toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = SSet.HomotopyCategory.homMk (edge s) := rfl

/-- 元の基本群の単位元は、元の基点の恒等射に移る。 -/
lemma toHom_one : toHom (1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x) = 𝟙 (SSet.HomotopyCategory.mk x) := by
  change SSet.HomotopyCategory.homMk (edge (.const : X.PtSimplex 1 x)) = _
  rw [edge_const, SSet.HomotopyCategory.homMk_id]

/-- 元の基本群の積は、元の辺の左から右の合成に移る。 -/
lemma toHom_mul (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x) :
    toHom (a * b) = toHom a ≫ toHom b := by
  induction a using Quotient.inductionOn with | h s => ?_
  induction b using Quotient.inductionOn with | h t => ?_
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec s t
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq r]
  exact (SSet.HomotopyCategory.homMk_comp_homMk (compStruct r)).symm

/-- 同じ元の辺のホモトピー圏の類が一致すれば、元の基本群の類も一致する。 -/
lemma toHom_injective : Function.Injective (toHom (X := X) (x := x)) := by
  rintro ⟨s⟩ ⟨t⟩ h
  have hfac : SSet.HomotopyCategory.homMk (edge (.const : X.PtSimplex 1 x)) ≫
      SSet.HomotopyCategory.homMk (edge s) = SSet.HomotopyCategory.homMk (edge t) := by
    rw [edge_const, SSet.HomotopyCategory.homMk_id, Category.id_comp]
    exact h
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hfac
  exact Quotient.sound ⟨mulStruct (SSet.Edge.CompStruct.ofTruncated r)⟩

/-- 元の基点の自己射は、元の境界定数一単体で表せる。 -/
lemma toHom_surjective : Function.Surjective (toHom (X := X) (x := x)) := by
  intro f
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x x f
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (simplex (SSet.Edge.ofTruncated e)), ?_⟩
  rw [toHom_mk, edge_simplex]
  exact he

/-- 元の基本群の類と、ホモトピー圏の同じ元の基点の自己射との全単射。 -/
def homEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x ≃
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk x) :=
  Equiv.ofBijective toHom ⟨toHom_injective, toHom_surjective⟩

local instance fundamentalLoopHomIsIso (f : SSet.HomotopyCategory.mk x ⟶
    SSet.HomotopyCategory.mk x) : IsIso f :=
  IsGroupoid.all_isIso (C := hoFunctor.obj X) f

/-- 元の基本群の逆元は、元のホモトピー圏の逆射に移る。 -/
lemma toHom_inv (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x) : toHom a⁻¹ = inv (toHom a) := by
  apply (cancel_mono (toHom a)).mp
  rw [← toHom_mul, inv_mul_cancel, toHom_one, IsIso.inv_hom_id]

end SerrePositivity.KST.Spectra.FundamentalLoop
