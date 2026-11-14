module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroCornerComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyInvertibility

/-!
概要：元実零角の二隣接辺を、端点成分を固定した元標準零角の辺と比較する。
方針：同じ toZeroCategory を零角の成分とし、全零関手比較を実正方形へ写す。
規約：元の四辺・二端点の道を厳密保持。使われ方：元上二胞体比較の全境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma zeroArrowSquareHomotopy (A B C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f.hom ≫ b.hom) (a.hom ≫ g.hom)) :
    ∃ H : SSet.Homotopy (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge)
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow g).edge),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow a).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow b).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.exists_arrowHomotopy_of_homMk_comm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow g).toTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow a).toTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow b).toTruncated
  have hi := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) f b).toTruncated
  have hj := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) a g).toTruncated
  let F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A D := ⟨f.hom ≫ b.hom,
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ f.isExact b.isExact⟩
  let G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A D := ⟨a.hom ≫ g.hom,
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ a.isExact g.isExact⟩
  exact hi.trans ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrow_homMk_eq_of_functorIso (F := F) (G := G) e).trans hj.symm)

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：元実零角から標準零角への同じ完全射は実可逆辺。
方針：既証明の同じ Cat^perf 零角同型の逆を完備包含で写す。
規約：元実零角を保持。使われ方：零角に隣接する二辺比較の同じ端点成分。 -/
lemma dgOdotMilnorNuZeroToZero_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).toTruncated := by
  have hi : IsIso ((hoFunctor.map perfectStableInfinityInclusion).toFunctor.map
      (dgOdotMilnorNuNullZeroVertexIso R d).inv) := inferInstance
  have he := perfectStableHoArrow_inclusion (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))
    (dgKInputStableValue_isIdempotentComplete R
      (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)))
    perfectZeroCategory_isIdempotentComplete
  change IsIso (stableHoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)))
  exact he ▸ hi

/-- 概要：元実左辺と元標準左辺を同じ指定端点成分で結ぶ実ホモトピー。
方針：零角への両合成の全零関手同型から元四辺を固定して実現する。
規約：始点成分は元核の恒等、終点成分は同じ実 toZeroCategory。使われ方：上比較 prism の左面。
-/
lemma exists_dgOdotMilnorNuZeroLeftArrowHomotopy :
    ∃ H : SSet.Homotopy
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K))).edge),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge := by
  apply zeroArrowSquareHomotopy (K) (Z) (K) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (dgOdotMilnorNuZeroActualLeft R d)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K)) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)
    (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)

/-- 概要：元左辺と元標準左辺を結ぶ同じ四辺固定ホモトピー。
方針：指定端点の道を持つ元存在証明から一つを取る。
規約：元の二辺・端点成分を保持。使われ方：元上二胞体の指定左面。 -/
def dgOdotMilnorNuZeroLeftArrowHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K))).edge) :=
  (exists_dgOdotMilnorNuZeroLeftArrowHomotopy R d).choose

/-- 概要：元左面の両端点の道は元核の恒等と同じ零角成分。
方針：同じ四辺固定存在証明の元端点式を使う。
規約：全一単体の等号。使われ方：隣接二面の厳密貼り合わせ。 -/
lemma dgOdotMilnorNuZeroLeftArrowHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroLeftArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroLeftArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge :=
  (exists_dgOdotMilnorNuZeroLeftArrowHomotopy R d).choose_spec

/-- 概要：元実上辺と元標準上辺を同じ指定端点成分で結ぶ実ホモトピー。
方針：同じ実零角の全零性と元完全射の零対象保存で元四辺を固定する。
規約：始点成分は同じ零角成分、終点成分は元商の恒等。使われ方：上比較 prism の上面。
-/
lemma exists_dgOdotMilnorNuZeroTopArrowHomotopy :
    ∃ H : SSet.Homotopy
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (B))).edge),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
  apply zeroArrowSquareHomotopy (Z) (B) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)
    (dgOdotMilnorNuZeroActualTop R d) (fromZeroCategory (B)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)) (𝟙 _)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _
    (fun _ => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ (dgOdotMilnorNuZeroActualTop R d).hom
      (dgOdotMilnorNuZeroActualTop R d).isExact _ (dgFixedNullInput_isZeroCategory R _ _))
    (fun x => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ (fromZeroCategory (B)).hom
      (fromZeroCategory (B)).isExact ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)).hom.app (Opposite.op ⦋0⦌) x)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

/-- 概要：元実上辺と元標準上辺を結ぶ同じ四辺固定ホモトピー。
方針：元の指定端点の道を持つ存在証明から一つを取る。
規約：元二辺・同じ零角成分を保持。使われ方：元上二胞体の指定上面。 -/
def dgOdotMilnorNuZeroTopArrowHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (B))).edge) :=
  (exists_dgOdotMilnorNuZeroTopArrowHomotopy R d).choose

/-- 概要：元上面の両端点の道は同じ零角成分と元商の恒等。
方針：同じ元存在証明の端点式を使う。
規約：全一単体の等号。使われ方：隣接二面の厳密貼り合わせ。 -/
lemma dgOdotMilnorNuZeroTopArrowHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroTopArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuZeroTopArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
  (exists_dgOdotMilnorNuZeroTopArrowHomotopy R d).choose_spec

end SerrePositivity.KST.SConstruction
