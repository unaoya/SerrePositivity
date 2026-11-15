module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：平坦な閉部分と指定開上の包含を、模型の実際の底変換へ渡す。
方針：pullback.lift の二射影の式と、pullback square の貼り合わせを使う。
規約：Rydh Proposition 3.7。底変換に平坦性を仮定しない。
使われ方：Noether 模型上の strictTransformι を C02 の入力に渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X Z S T : Scheme.{u}}

/-- 閉部分の射を同じ基底変更に沿って運ぶ、実際の pullback.lift。 -/
def closedRestrictionBaseChangeMap (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) :
    pullback (i ≫ f) v ⟶ pullback f v :=
  pullback.lift (pullback.fst (i ≫ f) v ≫ i) (pullback.snd (i ≫ f) v)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem closedRestrictionBaseChangeMap_fst (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) :
    closedRestrictionBaseChangeMap f i v ≫ pullback.fst f v =
      pullback.fst (i ≫ f) v ≫ i := by
  simp [closedRestrictionBaseChangeMap]

@[reassoc (attr := simp)]
theorem closedRestrictionBaseChangeMap_snd (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) :
    closedRestrictionBaseChangeMap f i v ≫ pullback.snd f v =
      pullback.snd (i ≫ f) v := by
  simp [closedRestrictionBaseChangeMap]

/-- 閉部分の実際の底変換射は、元の閉部分の射と pullback square を作る。 -/
theorem isPullback_closedRestrictionBaseChangeMap (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) :
    IsPullback (pullback.fst (i ≫ f) v) (closedRestrictionBaseChangeMap f i v)
      i (pullback.fst f v) := by
  have houter : IsPullback (pullback.fst (i ≫ f) v)
      (closedRestrictionBaseChangeMap f i v ≫ pullback.snd f v) (i ≫ f) v := by
    rw [closedRestrictionBaseChangeMap_snd]
    exact IsPullback.of_hasPullback _ _
  exact houter.of_bot (closedRestrictionBaseChangeMap_fst f i v).symm
    (IsPullback.of_hasPullback f v)

/-- 閉埋め込みの模型の底変換射も閉埋め込み。 -/
theorem isClosedImmersion_closedRestrictionBaseChangeMap
    (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) [IsClosedImmersion i] :
    IsClosedImmersion (closedRestrictionBaseChangeMap f i v) :=
  MorphismProperty.of_isPullback (isPullback_closedRestrictionBaseChangeMap f i v) inferInstance

/-- 平坦・局所有限表示・準コンパクトな閉部分の構造射は、同じ底変換後にもそうなる。 -/
theorem closedRestrictionBaseChangeMap_properties
    (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S)
    [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)] [QuasiCompact (i ≫ f)] :
    Flat (closedRestrictionBaseChangeMap f i v ≫ pullback.snd f v) ∧
    LocallyOfFinitePresentation (closedRestrictionBaseChangeMap f i v ≫ pullback.snd f v) ∧
    QuasiCompact (closedRestrictionBaseChangeMap f i v ≫ pullback.snd f v) := by
  rw [closedRestrictionBaseChangeMap_snd]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- 指定開の逆像を含む条件は、閉部分の同じ底変換へ渡る。 -/
theorem closedRestrictionBaseChangeMap_contains_preimage
    (f : X ⟶ S) (i : Z ⟶ X) (v : T ⟶ S) (U : S.Opens)
    (hU : ∀ x : X, f x ∈ U → x ∈ Set.range i)
    (x : (pullback f v : Scheme.{u})) (hx : pullback.snd f v x ∈ v ⁻¹ᵁ U) :
    x ∈ Set.range (closedRestrictionBaseChangeMap f i v) := by
  have hcomm : f (pullback.fst f v x) = v (pullback.snd f v x) :=
    congrArg (fun q : pullback f v ⟶ S ↦ q x) (pullback.condition (f := f) (g := v))
  obtain ⟨z, hz⟩ := hU (pullback.fst f v x) (by rw [hcomm]; exact hx)
  obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_closedRestrictionBaseChangeMap f i v) z x hz
  exact ⟨w, hw⟩

end SerrePositivity.AlgebraicGeometry
