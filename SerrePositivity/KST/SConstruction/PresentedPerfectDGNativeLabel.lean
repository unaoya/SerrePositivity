module
public import SerrePositivity.KST.SConstruction.DGNativePointLeft
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeActionFixed
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomWhiskering
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionClosedFamily
public import SerrePositivity.KST.SConstruction.DGFunctorClosedNativeEdge

/-! # 元の native Perf 関手族のラベル評価と同じ一回 Perf 延長
概要：元の全関手族を固定ラベルで評価し、同じ入力閉射の一回延長像へ戻す。
方針：左定数 tensor 単体と同じ dg 包含を使い、実 Hom 作用の比較共役を保持する。
規約：ラベルの対象を選び直さない。使われ方：固定 ν の比較辺の実 Perf 成分の回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

/-- 概要：元の signed swap と逆順の登録 braiding は相殺する。
方針：同じ複体の対称律を使う。規約：Hom の具体的成分を展開しない。
使われ方：ラベルを固定した右 tensor 作用の回収。 -/
lemma nativeLabel_signedSwap_braiding (R : Type u) [CommRing R]
    (P Q : Complex R) :
    (signedSwap P Q).hom ≫ (β_ Q P).hom = 𝟙 (P ⊗ Q) := by
  change (β_ P Q).hom ≫ (β_ Q P).hom = 𝟙 (P ⊗ Q)
  exact SymmetricCategory.symmetry P Q

variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]

/-- ラベルを固定した元の右 tensor 作用は、同じ元の入力 Hom の dg 作用。 -/
lemma presentedPerfectDGRightTensorAction_label (X : PresentedPerfectDGObject R D) :
    (dgTensorIncludeSecond R (PresentedPerfectDGObject R D) (DGFunctor R D E) X).comp
      (presentedPerfectDGRightTensorAction R D E) = presentedPerfectDGLabelAction R D E X := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro F G
  apply (Category.comp_id _).trans
  change dgTensorSecondHom R (PresentedPerfectDGObject R D) (DGFunctor R D E) X F G ≫
    (dgTensorBraidingHom R (PresentedPerfectDGObject R D) (DGFunctor R D E) (X, F) (X, G) ≫
      presentedPerfectDGTensorHom R D E F G X X) = _
  have hb : dgTensorSecondHom R (PresentedPerfectDGObject R D) (DGFunctor R D E) X F G ≫
      dgTensorBraidingHom R (PresentedPerfectDGObject R D) (DGFunctor R D E) (X, F) (X, G) =
      dgTensorFirstHom R (DGFunctor R D E) (PresentedPerfectDGObject R D) X F G := by
    change (freeUnitInsert R X (F ⟶[Complex R] G) ≫
      (signedSwap (F ⟶[Complex R] G) (X ⟶[Complex R] X)).hom) ≫
        (β_ (X ⟶[Complex R] X) (F ⟶[Complex R] G)).hom = _
    rw [Category.assoc, nativeLabel_signedSwap_braiding, Category.comp_id]
    rfl
  rw [← Category.assoc, hb]
  exact presentedPerfectDGTensorHom_first R D E X F G

/-- ラベルを同じ対象に固定した全 native 単体の作用は、元のラベル dg 作用の像。 -/
lemma presentedPerfectDGNativeActionSimplex_label {N : ℕ}
    (X : PresentedPerfectDGObject R D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R D E) N) :
    presentedPerfectDGNativeActionSimplex R D E
        (dgNativePointSimplex R (PresentedPerfectDGObject R D) X N) s =
      s.map (presentedPerfectDGLabelAction R D E X) := by
  unfold presentedPerfectDGNativeActionSimplex
  rw [dgNerveTensorSimplex_point_left]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (s.toSimplexData.map _).map _ = s.toSimplexData.map _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, presentedPerfectDGRightTensorAction_label]

/-- 元の全 native 関手族の各次数のラベル評価は、同じ dg 入力作用そのもの。 -/
lemma presentedPerfectDGNativeAction_label_app {N : ℕ}
    (X : PresentedPerfectDGObject R D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R D E) N) :
    (presentedPerfectDGNativeAction R D E).app (op ⦋N⦌)
        (dgNativePointSimplex R (PresentedPerfectDGObject R D) X N, ULift.up s) =
      s.map (presentedPerfectDGLabelAction R D E X) :=
  presentedPerfectDGNativeActionSimplex_label R D E X s

/-- 同じ native core の全パラメータでも、同じ元のラベル作用を厳密に回収する。 -/
lemma presentedPerfectDGNativeCoreAction_label_app {N : ℕ}
    (X : PresentedPerfectDGObject R D) (s : (dgFunctorNativeMappingSpace R D E) _⦋N⦌) :
    (presentedPerfectDGNativeCoreAction R D E).app (op ⦋N⦌)
        (dgNativePointSimplex R (PresentedPerfectDGObject R D) X N, ULift.up s) =
      s.val.map (presentedPerfectDGLabelAction R D E X) :=
  presentedPerfectDGNativeActionSimplex_label R D E X s.val

/-- 元の指定閉同型の native 辺の像は、同じ閉順射のラベル dg 作用の実辺。 -/
lemma presentedPerfectDGNativeCoreAction_label_closed
    (X : PresentedPerfectDGObject R D) (F G : DGFunctor R D E)
    (e : ForgetEnrichment.of (Complex R) F ≅ ForgetEnrichment.of (Complex R) G) :
    (presentedPerfectDGNativeCoreAction R D E).app (op ⦋1⦌)
        (dgNativePointSimplex R (PresentedPerfectDGObject R D) X 1,
          ULift.up (dgFunctorClosedIsoNativeEdge R D E F G e).edge) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (PresentedPerfectDGObject R E)
        ((presentedPerfectDGLabelAction R D E X).onClosed.map e.hom)).edge := by
  rw [presentedPerfectDGNativeCoreAction_label_app]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R (DGFunctor R D E) (presentedPerfectDGLabelAction R D E X) e.hom

/-- 同じラベル閉射の全 Hom は、元の一回 Perf 延長像と元の標準合成比較で回収できる。 -/
lemma presentedPerfectDGLabelAction_closed_perfect
    (X : PresentedPerfectDGObject R D) (F G : DGFunctor R D E)
    (a : ForgetEnrichment.of (Complex R) F ⟶ ForgetEnrichment.of (Complex R) G) :
    ForgetEnrichment.homTo (Complex R) ((presentedPerfectDGLabelAction R D E X).onClosed.map a) =
      ForgetEnrichment.homTo (Complex R)
        ((perfectDGExtensionInputFunctorAt R D E (presentedPerfectDGValue R D X)).onClosed.map a) ≫
          enrichedClosedIsoConjugation (Complex R) (presentedPerfectDGActionIso R D E F X)
            (presentedPerfectDGActionIso R D E G X) := by
  change ForgetEnrichment.homTo (Complex R) a ≫ presentedPerfectDGInputHom R D E F G X =
    (ForgetEnrichment.homTo (Complex R) a ≫
      perfectDGExtensionInputHom R D E F G (presentedPerfectDGValue R D X)) ≫ _
  rw [presentedPerfectDGInputHom_eq_perfect]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
