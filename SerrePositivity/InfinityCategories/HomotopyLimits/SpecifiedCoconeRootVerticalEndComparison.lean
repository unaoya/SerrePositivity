module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeCosliceSpecifiedHomotopy
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightRootBaseComparison
public import SerrePositivity.InfinityCategories.F1.TriangleLongEdge

/-!
概要：円柱の右端面を元の右四面体の全 Hom 族へ、終端を固定して接続する。
方針：同じ終端係数と指定した底の比較円柱を、相対 coslice の自明 Kan 射で持ち上げる。
規約：底は既存の円柱の raw な射そのもの。使われ方：共通 end 内の全 Hom 作用の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "a" => specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y
local notation "b" => specifiedCoconeRightRootTotalFamily hp p c hc dB dC y
local notation "H" => specifiedCoconeRightRootBaseComparison hp p c hc dB dC y
local notation "k" => stdSimplex.δ (0 : Fin 2)
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 指定した底の比較を保持し、元の右四面体族へ至る終端固定円柱が存在する。 -/
lemma exists_specifiedCoconeRootVerticalEndComparison :
    ∃ K : SSet.Homotopy a b,
      K.h ≫ sliceUnderRestrict V k = fst T Δ[1] ≫ b ≫ sliceUnderRestrict V k ∧
      K.h ≫ sliceUnderPostcomp V q = (H).h :=
  exists_relativeCosliceSpecifiedHomotopy V q k endpointInclusion_rightAnodyne a b
    (specifiedCoconeRootVerticalEndFamily_right_terminal hp p c hc dB dC y) H
    (specifiedCoconeRightRootBaseComparison_terminal hp p c hc dB dC y)

/-- 同じ右端面と元の右四面体族を、終端固定で結ぶ実際の円柱。 -/
def specifiedCoconeRootVerticalEndComparison : SSet.Homotopy a b :=
  (exists_specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).choose

/-- 元の右長辺族の上の終端係数を全時刻で固定する。 -/
lemma specifiedCoconeRootVerticalEndComparison_terminal :
    (specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).h ≫
        sliceUnderRestrict V k = fst T Δ[1] ≫ b ≫ sliceUnderRestrict V k :=
  (exists_specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).choose_spec.1

/-- 底は元の左右の根辺比較円柱の同じ表示変更そのもの。 -/
lemma specifiedCoconeRootVerticalEndComparison_base :
    (specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).h ≫ sliceUnderPostcomp V q =
      (H).h :=
  (exists_specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).choose_spec.2

/-- 可変終点の全族も、元の右族のまま全時刻で固定する。 -/
lemma specifiedCoconeRootVerticalEndComparison_projection :
    (specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).h ≫ sliceUnderProjection V =
      fst T Δ[1] ≫ b ≫ sliceUnderProjection V := by
  have h := congrArg (fun m ↦ m ≫ sliceUnderProjection (k ≫ V))
    (specifiedCoconeRootVerticalEndComparison_terminal hp p c hc dB dC y)
  simpa only [Category.assoc, sliceUnderRestrict_projection] using h

/-- 比較の底の終点は、元の指定 y で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalEndComparison_fixed :
    ((specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).h ≫
      sliceUnderProjection V) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalEndComparison_projection]
  have h := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m)
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)
  simpa only [specifiedCoconeRightRootTotalFamily, Category.assoc,
    sliceUnderRestrict_projection, SSet.comp_const] using h

/-- 正規化後の底も、元の同じ fiber 比較円柱を包含した raw な射そのもの。 -/
lemma specifiedCoconeRootVerticalEndComparison_native_base :
    ((specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y).h ≫
      sliceUnderPostcomp V q) ≫ eqToHom (congrArg sliceUnder
        (specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC)) =
      (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h ≫
        vertexFiberι (sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC)) y := by
  rw [specifiedCoconeRootVerticalEndComparison_base, specifiedCoconeRightRootBaseComparison_raw]
  change ((specifiedCoconeRootBaseFamilyComparison hp p c hc dB dC y).h ≫
      (eqToIso (congrArg sliceUnder
        (specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC))).inv) ≫
      (eqToIso (congrArg sliceUnder
        (specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC))).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    specifiedCoconeRootBaseFamilyComparison_raw]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
