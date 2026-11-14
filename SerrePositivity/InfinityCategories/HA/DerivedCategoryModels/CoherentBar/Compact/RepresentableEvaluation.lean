module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedComplexModelComparison
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Basic
/-!
概要：代表可能加群からの全次数 Hom を評価複体へ移す比較を与える。
方針：dg Yoneda の単位元評価を使い、任意次数の後合成と Koszul 符号を照合する。
規約：H⁰ に切り詰めず、全次数と全 pinched 単体を保つ。
使われ方：coherent な filtered 比較を消費する c2 の評価計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded Opposite CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 代表からの任意次数の Hom の評価は、任意次数の後合成と整合する。 -/
lemma dgBarCompactYoneda_forward (x : D) (M N : RightModule R D)
    {p q n : ℤ} (t : GradedHom R (representable R x) M p)
    (f : GradedHom R M N q) (hn : p + q = n) :
    (dgYonedaIso R x N).hom.f n
        (forward R (D := RightModule R D) t f hn) =
      (p * q).negOnePow •
        (((moduleHomπ R D M N x).f q f).v p n hn
          ((dgYonedaIso R x M).hom.f p t)) := by
  change (yonedaEvaluateFamily R x N
    (fun y => moduleHomπ R D (representable R x) N y.unop)).f n _ = _
  rw [yonedaEvaluateFamily_apply, moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hn 0 p n (zero_add p) hn]
  simp only [dgYonedaIso, yonedaEvaluateFamily_apply, Units.smul_def,
    ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.comp_apply]

/-- 共変 Hom の豊穣作用の符号と後合成の符号は相殺し、評価作用そのものになる。 -/
lemma dgBarCompactYoneda_leftAction (x : D) (M N : RightModule R D)
    {p q n : ℤ} (f : GradedHom R M N q)
    (t : (moduleHom R D (representable R x) M).X p) (hn : p + q = n) :
    (dgYonedaIso R x N).hom.f n
        (leftAction R (leftRepresentable R (representable R x)) f t hn) =
      (((moduleHomπ R D M N x).f q f).v p n hn
        ((dgYonedaIso R x M).hom.f p t)) := by
  rw [leftRepresentable_action]
  simp only [Units.smul_def, map_zsmul]
  rw [dgBarCompactYoneda_forward R D x M N t f hn]
  rw [Units.smul_def, smul_smul, mul_comm q p, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

/-- 全 Hom 複体の同型を通して得る、実 pinched 空間と評価複体の同型。 -/
def dgBarCompactRepresentablePinchedIso (x : D) (M : RightModule R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom.{u, max (u + 1) v} R (RightModule R D) (representable R x) M ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (M.obj (op x)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (representable R x) M ≪≫
    { hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (dgYonedaIso R x M).hom
      inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (dgYonedaIso R x M).inv
      hom_inv_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id]
      inv_hom_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id] }

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
