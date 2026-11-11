module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismSideHomotopies
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryFaceGluing
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyFilling

/-!
概要：元上下二胞体の指定三側面を実際の三角形境界の全族として貼る。
方針：同じ端点経路の厳密一致を転置し、既存の全指定面の境界貼り合わせへ渡す。
規約：元の全側面を保持。内部三単体の充填や Verdier 全比較は主張しない。
使われ方：元二胞体を固定する比較 prism の同じ全側境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元三角形の面番号に沿う同じ最後・対角・最初の比較側面。
方針：元の三実ホモトピーの全射を同じ順に束ねる。
規約：全パラメータを保持。使われ方：元全側境界の指定三面。 -/
def dgOdotMilnorNuNullPrismSideFamily (j : Fin 2) (i : Fin 3) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  ![(dgOdotMilnorNuNullPrismLastHomotopy R d h j).h,
    (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h,
    (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h] i

/-- 概要：同じ元三側面の転置は全共有面上で厳密に一致する。
方針：元始点・中間点・終点の三つの全経路等号を転置する。
規約：元の全一単体。使われ方：元指定三面を貼る整合性。 -/
lemma dgOdotMilnorNuNullPrismSideFamily_compatible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryFaceCompatible (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose (Δ[1] : SSet.{u + 2})
      Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullPrismSideFamily R d h j i)) := by
  have transposed {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}}
      {a b : (Δ[0] : SSet.{u + 2}) ⟶ Δ[1]}
      (he : (a ▷ Δ[1]) ≫ f = (b ▷ Δ[1]) ≫ g) :
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} f =
        b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} g := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose_precomp]
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[0] Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) he
  intro a b hab
  fin_cases a <;> fin_cases b <;> try norm_num at hab
  · change stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h =
      stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h
    exact transposed (dgOdotMilnorNuNullPrismSide_target R d h j)
  · change stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h =
      stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h
    exact transposed (dgOdotMilnorNuNullPrismSide_middle R d h j).symm
  · change stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h =
      stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose Δ[1] Δ[1]
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h
    exact transposed (dgOdotMilnorNuNullPrismSide_source R d h j).symm

/-- 概要：元三比較側面を保持する実際の三角形全境界上の区間族。
方針：同じ転置整合族を境界に貼り、元の積の族へ戻す。
規約：元の側面を取り替えない。使われ方：全四面回収の同じ側境界。 -/
def dgOdotMilnorNuNullPrismSideBoundary (j : Fin 2) :
    (boundary 2 : SSet.{u + 2}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose (boundary 2 : SSet.{u + 2}) Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.boundaryFaceGluing (dgOdotMilnorNuNullPrismSideFamily_compatible R d h j))

/-- 概要：貼った全側境界は同じ元三実ホモトピーを全単体で厳密回収する。
方針：転置の単射性と既存の全指定面回収を使う。
規約：全三面の厳密等号。使われ方：元比較 prism の指定側面の保持。 -/
lemma dgOdotMilnorNuNullPrismSideBoundary_faces (j : Fin 2) (i : Fin 3) :
    (boundary.ι i ▷ (Δ[1] : SSet.{u + 2})) ≫
        dgOdotMilnorNuNullPrismSideBoundary R d h j =
      dgOdotMilnorNuNullPrismSideFamily R d h j i := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose (Δ[1] : SSet.{u + 2}) Δ[1] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose_precomp]
  change boundary.ι i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose (boundary 2 : SSet.{u + 2}) Δ[1]
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyRightTranspose (boundary 2 : SSet.{u + 2}) Δ[1]
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).symm _) = _
  rw [Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.boundaryFaceGluing_face]

end SerrePositivity.KST.SConstruction
