module

public import SerrePositivity.CategoryTheory.KaroubiExtensionOne
public import SerrePositivity.CategoryTheory.VerdierLift
public import SerrePositivity.CategoryTheory.TExactKernelQuotient
public import Mathlib.CategoryTheory.Triangulated.Generators

/-! # Verdier 商と冪等完備化の交換

元の零部分圏の像が生成する厚い部分圏で割り、最後に完備化した圏を比較する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 512

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/-- 完備化した圏の中で、元の零部分圏の像が生成する厚い部分圏。 -/
abbrev karoubiNullEnvelope : ObjectProperty (Karoubi C) :=
  (P.map (toKaroubi C)).triangEnvelope

/-- 完備化を先に行った Verdier 商。 -/
abbrev KaroubiFirstQuotient := (karoubiNullEnvelope P).trW.Localization

/-- 元の商関手の完備化への延長。 -/
noncomputable abbrev karoubiQuotientExtension : Karoubi C ⥤ Karoubi P.trW.Localization :=
  (functorExtension₂ _ _).obj P.trW.Q

/-- 三角関手の核は直和因子で閉じている。 -/
instance triangulatedKernel_stableUnderRetracts
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    (triangulatedKernel F).IsStableUnderRetracts where
  of_retract r h := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← (r.map F).retract]
    change F.map r.i ≫ F.map r.r = 0
    rw [h.eq_of_tgt (F.map r.i) 0, zero_comp]

/-- 延長した商関手は厚い零部分圏を消す。 -/
lemma karoubiQuotientExtension_kills (X : Karoubi C) (hX : karoubiNullEnvelope P X) :
    IsZero ((karoubiQuotientExtension P).obj X) := by
  have h : karoubiNullEnvelope P ≤ triangulatedKernel (karoubiQuotientExtension P) := by
    refine ((P.map (toKaroubi C)).triangEnvelope_le_iff
      (Q := triangulatedKernel (karoubiQuotientExtension P))).mpr ?_
    rintro Y ⟨Z, hZ, ⟨i⟩⟩
    let F := karoubiQuotientExtension P
    have hz := (toKaroubi _).map_isZero (verdierQuotient_isZero P Z hZ)
    let e : F.obj ((toKaroubi C).obj Z) ≅ (toKaroubi _).obj (P.trW.Q.obj Z) :=
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app P.trW.Q).app Z
    exact (hz.of_iso e).of_iso (F.mapIso i.symm)
  exact h X hX

/-- 完備化を先に行った商から、後に行った完備化への関手。 -/
noncomputable abbrev karoubiFirstToLast : KaroubiFirstQuotient P ⥤ Karoubi P.trW.Localization :=
  verdierLift (karoubiNullEnvelope P) (karoubiQuotientExtension P)
    (karoubiQuotientExtension_kills P)

/-- 逆向きの比較を作るための、元の圏からの関手。 -/
noncomputable abbrev karoubiFirstFromOriginal : C ⥤ Karoubi (KaroubiFirstQuotient P) :=
  toKaroubi C ⋙ (karoubiNullEnvelope P).trW.Q ⋙ toKaroubi _

lemma karoubiFirstFromOriginal_kills (X : C) (hX : P X) :
    IsZero ((karoubiFirstFromOriginal P).obj X) :=
  (toKaroubi _).map_isZero (verdierQuotient_isZero (karoubiNullEnvelope P) _
    ((P.map (toKaroubi C)).le_triangEnvelope _ (P.prop_map_obj _ hX)))

noncomputable abbrev karoubiLastToFirst : P.trW.Localization ⥤ Karoubi (KaroubiFirstQuotient P) :=
  verdierLift P (karoubiFirstFromOriginal P) (karoubiFirstFromOriginal_kills P)

/-- 両側を完備化した後の順方向の比較関手。 -/
noncomputable abbrev completedKaroubiFirstToLast :
    Karoubi (KaroubiFirstQuotient P) ⥤ Karoubi P.trW.Localization :=
  (functorExtension₁ _ _).obj (karoubiFirstToLast P)

/-- 両側を完備化した後の逆方向の比較関手。 -/
noncomputable abbrev completedKaroubiLastToFirst :
    Karoubi P.trW.Localization ⥤ Karoubi (KaroubiFirstQuotient P) :=
  (functorExtension₁ _ _).obj (karoubiLastToFirst P)

noncomputable def karoubiFirstToLastFactors :
    (karoubiNullEnvelope P).trW.Q ⋙ karoubiFirstToLast P ≅ karoubiQuotientExtension P :=
  verdierLiftFactors _ _ _

noncomputable def karoubiLastToFirstFactors :
    P.trW.Q ⋙ karoubiLastToFirst P ≅ karoubiFirstFromOriginal P :=
  verdierLiftFactors _ _ _

noncomputable def completedKaroubiFirstToLastFactors :
    toKaroubi _ ⋙ completedKaroubiFirstToLast P ≅ karoubiFirstToLast P :=
  (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app _

noncomputable def completedKaroubiLastToFirstFactors :
    toKaroubi _ ⋙ completedKaroubiLastToFirst P ≅ karoubiLastToFirst P :=
  (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app _

/-- 完備化を先に行った側での比較関手の往復同型。 -/
noncomputable def completedKaroubiFirstRoundTrip :
    completedKaroubiFirstToLast P ⋙ completedKaroubiLastToFirst P ≅ 𝟭 _ := by
  let L := completedKaroubiFirstToLast P
  let G := completedKaroubiLastToFirst P
  let Q := (karoubiNullEnvelope P).trW.Q
  let K := toKaroubi (KaroubiFirstQuotient P)
  let e : toKaroubi C ⋙ Q ⋙ K ⋙ L ⋙ G ≅ toKaroubi C ⋙ Q ⋙ K :=
    isoWhiskerLeft (toKaroubi C ⋙ Q)
      (isoWhiskerRight (completedKaroubiFirstToLastFactors P) G) ≪≫
    isoWhiskerLeft (toKaroubi C) (isoWhiskerRight (karoubiFirstToLastFactors P) G) ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app P.trW.Q) G ≪≫
    isoWhiskerLeft P.trW.Q (completedKaroubiLastToFirstFactors P) ≪≫
    karoubiLastToFirstFactors P
  let e' : Q ⋙ K ⋙ L ⋙ G ≅ Q ⋙ K :=
    ((whiskeringLeft _ _ _).obj (toKaroubi C)).preimageIso e
  let e'' : K ⋙ L ⋙ G ≅ K :=
    (Localization.fullyFaithfulWhiskeringLeft Q (karoubiNullEnvelope P).trW _).preimageIso e'
  exact ((whiskeringLeft _ _ _).obj K).preimageIso e''

/-- 元の商を先に取った側での比較関手の往復同型。 -/
noncomputable def completedKaroubiLastRoundTrip :
    completedKaroubiLastToFirst P ⋙ completedKaroubiFirstToLast P ≅ 𝟭 _ := by
  let L := completedKaroubiFirstToLast P
  let G := completedKaroubiLastToFirst P
  let Q := (karoubiNullEnvelope P).trW.Q
  let K := toKaroubi P.trW.Localization
  let e : P.trW.Q ⋙ K ⋙ G ⋙ L ≅ P.trW.Q ⋙ K :=
    isoWhiskerLeft P.trW.Q (isoWhiskerRight (completedKaroubiLastToFirstFactors P) L) ≪≫
    isoWhiskerRight (karoubiLastToFirstFactors P) L ≪≫
    isoWhiskerLeft (toKaroubi C ⋙ Q) (completedKaroubiFirstToLastFactors P) ≪≫
    isoWhiskerLeft (toKaroubi C) (karoubiFirstToLastFactors P) ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app P.trW.Q
  let e' : K ⋙ G ⋙ L ≅ K :=
    (Localization.fullyFaithfulWhiskeringLeft P.trW.Q P.trW _).preimageIso e
  exact ((whiskeringLeft _ _ _).obj K).preimageIso e'

instance completedKaroubiFirstToLast_isEquivalence :
    (completedKaroubiFirstToLast P).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (completedKaroubiFirstToLast P) (completedKaroubiLastToFirst P)
    (completedKaroubiFirstRoundTrip P).symm (completedKaroubiLastRoundTrip P)).isEquivalence_functor

/-- 商と完備化の順序を交換する圏同値。比較関手はともに三角関手である。 -/
noncomputable def karoubiVerdierOrderEquivalence :
    Karoubi (KaroubiFirstQuotient P) ≌ Karoubi P.trW.Localization :=
  (completedKaroubiFirstToLast P).asEquivalence

end SerrePositivity
