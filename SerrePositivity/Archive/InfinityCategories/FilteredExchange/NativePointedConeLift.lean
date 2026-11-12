module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-!
概要：native な錐全体を、指定した始点の族を保って pointed space へ持ち上げる。
方針：錐の頂点包含の left anodyne 性と始点固定の相対延長空間を使う。
規約：図式・始点・全パラメータを保持。使われ方：二三角形を共通の全錐で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
local notation "V" => join Δ[0] K
local notation "i" => joinInl Δ[0] K ▷ A
local notation "v" => snd Δ[0] A ≫ s
local notation "b" => fst V A ≫ c.val

include hs
/-- 指定した始点族の底は、全錐図式の頂点への制限に厳密に等しい。 -/
lemma nativePointedCone_initial : v ≫ pointedSpaceProjection = i ≫ b := by
  have hc : joinInl (Δ[0] : SSet.{u + 1}) K ≫ c.val = SSet.const c.vertex := by
    have h := (SSet.yonedaEquiv.symm_apply_apply (joinInl Δ[0] K ≫ c.val)).symm
    change joinInl Δ[0] K ≫ c.val = SSet.yonedaEquiv.symm c.vertex at h
    rwa [SSet.yonedaEquiv_symm_zero] at h
  rw [Category.assoc, hs, ← Category.assoc i, whiskerRight_fst, Category.assoc, hc]
  simp only [SSet.comp_const]

/-- 全錐の持ち上げの高次の選択空間。元の始点族を型に保持する。 -/
def nativePointedConeExtensionSpace : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection b i v (nativePointedCone_initial c s hs)

/-- 始点固定の全錐の持ち上げの選択空間は可縮な Kan 複体。 -/
lemma nativePointedConeExtensionSpace_contractible :
    IsContractibleKan (nativePointedConeExtensionSpace c s hs) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (joinPoint_inl_leftAnodyne K) A)
    v (nativePointedCone_initial c s hs)

/-- 同じ全錐と始点族を保つ pointed な全持ち上げが存在する。 -/
lemma nativePointedConeLift_exists :
    ∃ L : V ⊗ A ⟶ PointedSpaceInfinity.{u}, L ≫ pointedSpaceProjection = b ∧ i ≫ L = v :=
  exists_relativeFunctorExtension_of_leftAnodyne pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (joinPoint_inl_leftAnodyne K) A)
    v (nativePointedCone_initial c s hs)

/-- 始点族と元の全錐を保つ一つの全持ち上げ。比較は可縮な選択空間内で行う。 -/
def nativePointedConeLift : V ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (nativePointedConeLift_exists c s hs).choose

lemma nativePointedConeLift_projection :
    nativePointedConeLift c s hs ≫ pointedSpaceProjection = b :=
  (nativePointedConeLift_exists c s hs).choose_spec.1

lemma nativePointedConeLift_initial : i ≫ nativePointedConeLift c s hs = v :=
  (nativePointedConeLift_exists c s hs).choose_spec.2

end SerrePositivity.InfinityCategories.F2
