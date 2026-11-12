module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：coherent Hom 比較の豊穣関手に関する自然性。
方針：比較を定める thickening 上の豊穣関手を対象と Hom の作用で比較する。
規約：局所 Kan 性を要求せず、全次数の単体を比較する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Remark 4.6.7.9（Tag 01LH）、評価関手と写像空間比較の整合性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coherent Hom の比較単体は豊穣関手による後合成と可換。
方針：最後の対象とそれ以前の対象に分け、非定値 Hom は Yoneda の自然性で比較する。
規約：始域と標的の対象の宇宙 v、Hom の宇宙 u を共有する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、評価の豊穣的な作用を coherent な単体へ移す。 -/
lemma coherentHomComparisonSimplex_postcomp
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex σ).comp SSet F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((F.map X Y).app (Opposite.op ⦋n⦌) σ) := by
  have hobj (i : Fin (n + 2)) :
      F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (F.obj X) (F.obj Y) i := by
    induction i using Fin.lastCases <;>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]
  have hm {A B A' B' : C} (ha : A = A') (hb : B = B') :
      F.map A B ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg F.obj ha) (congrArg F.obj hb)) =
      eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) ≫ F.map A' B' := by
    subst A'
    subst B'
    simp
  have hn (i j : Fin (n + 2)) {A B : C}
      (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y i = A)
      (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y j = B)
      (hi' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (F.obj X) (F.obj Y) i = F.obj A)
      (hj' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (F.obj X) (F.obj Y) j = F.obj B)
      (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ i j ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)) ≫ F.map A B =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map X Y).app (Opposite.op ⦋n⦌) σ) i j ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hi' hj')) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ i j ≫ F.map _ _) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (hobj i) (hobj j)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom ((F.map X Y).app (Opposite.op ⦋n⦌) σ) i j := by
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom hi' hj'))).mp
    simp only [Category.assoc, eqToHom_trans]
    have hh := hm hi hj
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ i j ≫ F.map _ _ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (congrArg F.obj hi) (congrArg F.obj hj)) = _
    rw [hh, ← Category.assoc]
    exact h
  apply EnrichedFunctor.ext SSet (fun i ↦ hobj i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change Fin (n + 2) at i j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ i j ≫ F.map _ _) ≫ eqToHom _ = _
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · apply hn _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj X) (F.obj Y) n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj X) (F.obj Y) n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last,
      Category.assoc, F.map_id]
  · rename_i j
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    exact False.elim ((Nat.not_le_of_lt j.isLt) h)
  · rename_i i
    apply hn _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj X) (F.obj Y) i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (F.obj X) (F.obj Y) n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last, Category.assoc,
      SSet.yonedaEquiv_symm_comp]
  · rename_i i j
    apply hn _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj X) (F.obj Y) i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (F.obj X) (F.obj Y) j)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast,
      Category.assoc, F.map_id]

/-- 概要：右 pinched 写像空間の端点の等号による移送は元の coherent 単体を変えない。
方針：二つの端点の等号を消去する。
規約：標的の充填性は不要。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、coherent nerve の像の端点の正規化。 -/
lemma pinchedHom_eqToHom_app_val {Z : SSet.{u}} {x y x' y' : Z _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋n⦌) :
    (((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b) hx hy)).app (Opposite.op ⦋n⦌)) s).val =
      s.val := by
  subst x'
  subst y'
  rfl

/-- 概要：豊穣関手が coherent nerve の標準二頂点間の写像空間に誘導する射。
方針：coherent nerve の射による作用の後、標準頂点への端点の等号で正規化する。
規約：通常の pinchedHomMap と端点の同型の合成。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、豊穣 Hom の比較との自然性の可換図式。 -/
noncomputable def coherentPinchedHomMap {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) ≫
    eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F Y))

/-- 概要：coherent Hom 比較は豊穣関手の Hom 上の作用と coherent nerve 上の作用を全次数で結ぶ。
方針：各単体で端点の移送を外し、比較単体の後合成公式を適用する。
規約：Hom の宇宙を対象の宇宙へ持ち上げる射を左上に置く。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Remark 4.6.7.9（Tag 01LH）、写像空間の同値性を評価関手に移す。 -/
lemma coherentHomComparison_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y ≫ coherentPinchedHomMap F X Y =
      (SSet.uliftFunctor.{v, u}).map (F.map X Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (F.obj X) (F.obj Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  change (((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F Y))).app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) _ _).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app _ σ))).val = _
  rw [pinchedHom_eqToHom_app_val (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F Y)]
  exact coherentHomComparisonSimplex_postcomp F σ.down

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
