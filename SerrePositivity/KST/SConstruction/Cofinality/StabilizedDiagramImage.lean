module
public import SerrePositivity.KST.SConstruction.Cofinality.DiagramImage
public import SerrePositivity.KST.SConstruction.Cofinality.MultiDiagramImage
public import SerrePositivity.KST.SConstruction.SClosedPredicates
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroNaturality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
概要：点ごとの補対象供給を、同じ完全射の有限 S 図式の本質像条件へ接続する。
方針：S_n の完全な Ar 評価が双積と一回シフトを保つことを使う。
規約：点ごとの密度入力は供給境界であり、一般の共終性の追加仮定にはしない。
使われ方：D-22 の到着時に同じ指定射の S_n 安定化へ代入する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ有限 S 図式の双積懸垂を評価すると、元の値の双積懸垂に同型。
方針：完全な評価の双積比較とシフト比較を合成する。
規約：元の Ar 評価を使い、各成分に新しい射を選ばない。
使われ方：点ごとの補対象を有限 S 図式へ接続する評価式。 -/
def sEvaluationBiprodShiftIso (n : ℕ) (Y : StableModel.{u})
    (a : (arNerve n) _⦋0⦌) (d : hoFunctor.obj ((sStableModel n Y).carrier)) :
    (hoFunctor.map (sStableEvaluation n Y a).val).toFunctor.obj
      (biprod d ((shiftFunctor (hoFunctor.obj ((sStableModel n Y).carrier)) (1 : ℤ)).obj d)) ≅
    biprod ((hoFunctor.map (sStableEvaluation n Y a).val).toFunctor.obj d)
      ((shiftFunctor (hoFunctor.obj Y.carrier) (1 : ℤ)).obj
        ((hoFunctor.map (sStableEvaluation n Y a).val).toFunctor.obj d)) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (sStableEvaluation n Y a).val := stableModelHom_exact _
  let E := (hoFunctor.map (sStableEvaluation n Y a).val).toFunctor
  let : E.Additive := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctor_additive _
  let : PreservesFiniteBiproducts E := Functor.preservesFiniteBiproductsOfAdditive E
  let : PreservesBinaryBiproducts E := preservesBinaryBiproducts_of_preservesBiproducts E
  exact E.mapBiprod d _ ≪≫ biprod.mapIso (Iso.refl _) ((E.commShiftIso (1 : ℤ)).app d)

/-- 概要：点ごとの補対象供給から、有限 S 図式の双積懸垂が同じ S_n 射の本質像に入る。
方針：完全な評価で供給型へ戻し、全 Ar 図式の回収を適用する。
規約：密度供給だけに条件付きの補助結果であり、一般共終性は主張しない。
使われ方：D-22 の同じ射への特殊化を有限 S 図式へ持ち上げる。 -/
lemma sBiprodShift_mem_image_of_density (n : ℕ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val)
    (hdensity : ∀ d : hoFunctor.obj Y.carrier, ∃ c : hoFunctor.obj X.carrier,
      Nonempty (biprod d ((shiftFunctor (hoFunctor.obj Y.carrier) (1 : ℤ)).obj d) ≅
        (hoFunctor.map f.val).toFunctor.obj c))
    (d : hoFunctor.obj ((sStableModel n Y).carrier)) :
    ∃ c : hoFunctor.obj ((sStableModel n X).carrier),
      Nonempty (biprod d ((shiftFunctor (hoFunctor.obj ((sStableModel n Y).carrier))
        (1 : ℤ)).obj d) ≅ (hoFunctor.map ((sEndofunctor n).map f).val).toFunctor.obj c) := by
  let w := biprod d ((shiftFunctor (hoFunctor.obj ((sStableModel n Y).carrier)) (1 : ℤ)).obj d)
  obtain ⟨y, hy⟩ := SSet.Truncated.HomotopyCategory.mk_surjective w
  have himage (a : (arNerve n) _⦋0⦌) : ∃ x : X.carrier _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x)
        ((gappedDiagram y).app (Opposite.op ⦋0⦌) a)) := by
    let E := (hoFunctor.map (sStableEvaluation n Y a).val).toFunctor
    obtain ⟨c, ⟨e⟩⟩ := hdensity (E.obj d)
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective c
    refine ⟨x, ⟨?_⟩⟩
    have he : E.obj (HomotopyCategory.mk y) ≅
        biprod (E.obj d) ((shiftFunctor (hoFunctor.obj Y.carrier) (1 : ℤ)).obj (E.obj d)) :=
      E.mapIso (eqToIso hy) ≪≫ sEvaluationBiprodShiftIso n Y a d
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram y) = y.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) Y.carrier).apply_symm_apply y.val
    have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex a (gappedDiagram y)
    rw [hv] at ha
    exact e.symm ≪≫ he.symm ≪≫ eqToIso (congrArg HomotopyCategory.mk ha)
  obtain ⟨x, ⟨e⟩⟩ := exists_sVertexIso_of_pointwise_image f hf y himage
  exact ⟨HomotopyCategory.mk x, ⟨(eqToIso hy).symm ≪≫ e.symm⟩⟩

/-- 概要：点ごとの補対象供給は独立な全多次数の反復 S の双積懸垂へ持ち上がる。
方針：同じ完全射の S_n 安定化の像回収を反復数について帰納する。
規約：各多次数を保持し、異なる多次数で独立に選んだ像の自然性は結論しない。
使われ方：反復 S の実現へ進む前の有限図式の補対象回収。 -/
lemma multiSBiprodShift_mem_image_of_density (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val)
    (hdensity : ∀ d : hoFunctor.obj Y.carrier, ∃ c : hoFunctor.obj X.carrier,
      Nonempty (biprod d ((shiftFunctor (hoFunctor.obj Y.carrier) (1 : ℤ)).obj d) ≅
        (hoFunctor.map f.val).toFunctor.obj c))
    (d : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    ∃ c : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj X).carrier,
      Nonempty (biprod d ((shiftFunctor
        (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) (1 : ℤ)).obj d) ≅
          (hoFunctor.map (((multiSEndofunctor r).obj ι).map f).val).toFunctor.obj c) := by
  induction r generalizing X Y with
  | zero => exact hdensity d
  | succ r ih =>
    exact sBiprodShift_mem_image_of_density (ι 0).unop.len
      (((multiSEndofunctor r).obj (fun i => ι i.succ)).map f)
      (multiSEndofunctor_map_isFullyFaithful r _ f hf)
      (ih (fun i => ι i.succ) f hf hdensity) d

end SerrePositivity.KST.SConstruction.Cofinality
