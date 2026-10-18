module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexCone
public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableShift
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps
public import SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit

/-!
# 代表加群の射と cone の具体的表示

概要：複体の chain map による後合成を全次数自然な代表加群の射として構成する。
方針：cochain の結合則を使い、同じ後合成の族から cone 加群を作る。
規約：評価した chain map を保ち、cone の比較に別の射を選ばない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

attribute [local instance] enrichment

/--
概要：通常の後合成の族は代表 dg 加群の全次数の作用と両立する。
方針：符号付き前合成と次数零の後合成の結合則を使う。
規約：次数零の自然性だけには制限しない。
使われ方：Drinfeld §2.4、KST D4 の cone に入れる代表加群の射。
-/
theorem representablePostcompose_naturality {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z)
    (x y : (CochainComplex C ℤ)ᵒᵖ) :
    (representable A Y).map x y ≫ homPostcompose _ (mappingPostcompose A y.unop f) =
      (representable A Z).map x y ≫ homPrecompose (mappingPostcompose A x.unop f) _ := by
  apply closedFamily_of_action A (M := representable A Y) (N := representable A Z)
    (fun t => mappingPostcompose A t.unop f) ?_ x y
  intro x y p r n hn a b
  unfold moduleAction
  rw [representableMap_apply, representableMap_apply, forward_cochain, forward_cochain]
  change ((p * r).negOnePow • a.comp b (by omega)).comp (Cochain.ofHom f) (add_zero n) =
    (p * r).negOnePow • a.comp (b.comp (Cochain.ofHom f) (add_zero r)) (by omega)
  rw [Cochain.units_smul_comp, Cochain.comp_assoc_of_third_is_zero_cochain]

/--
概要：同じ成分族から作った cone dg 加群は自然性の証明によらず一致する。
方針：成分族の等式で置換し、証明の無関係性を使う。
規約：自然性は両辺で証明済み。
使われ方：Drinfeld §2.4、KST D4 の標準 cone と具体的成分表示の接続。
-/
theorem coneModule_family_congr {M N : RightModule A (CochainComplex C ℤ)}
    {a b : ∀ x, M.obj x ⟶ N.obj x}
    (ha : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y))
    (hb : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (b y) =
      N.map x y ≫ homPrecompose (b x) (N.obj y)) (h : a = b) :
    coneModule M N a ha = coneModule M N b hb := by
  cases h
  rfl

variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：複体の chain map による代表 dg 加群の後合成射。
方針：具体的な後合成の chain map 族と全次数自然性を束ねる。
規約：元の chain map をそのまま用いる。
使われ方：Drinfeld §2.4、KST D4 の代表加群の cone。
-/
def representablePostcompose {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    ForgetEnrichment.of (Complex A) (representable A Y) ⟶
      ForgetEnrichment.of (Complex A) (representable A Z) :=
  moduleMorphismMk A (CochainComplex C ℤ) (fun x => mappingPostcompose A x.unop f)
    (representablePostcompose_naturality A f)

/--
概要：代表加群の後合成射を評価すると写像複体の後合成に戻る。
方針：全次数自然な射族からの構成の評価公式を使う。
規約：同じ具体的な chain map を保つ。
使われ方：Drinfeld §2.4、KST D4 の cone の比較正方形。
-/
lemma representablePostcompose_eval {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z)
    (T : CochainComplex C ℤ) :
    (moduleEvaluation A (CochainComplex C ℤ) T).map (representablePostcompose A f) =
      mappingPostcompose A T f := moduleMorphismMk_eval A (CochainComplex C ℤ) _ _ T

/--
概要：代表加群の後合成射の、具体的な写像複体ごとの cone。
方針：同じ後合成の全次数自然な族から既存 coneModule を構成する。
規約：これは証明済みの cone 構成であり、代表可能性は別途証明する。
使われ方：Drinfeld §2.4、KST D4 の cone の代表可能性。
-/
abbrev representableConeModule {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    RightModule A (CochainComplex C ℤ) :=
  coneModule (representable A Y) (representable A Z)
    (fun x => mappingPostcompose A x.unop f) (representablePostcompose_naturality A f)

variable [HasBinaryBiproducts C]

/--
概要：cone の写像複体の比較は代表加群の全次数の作用と両立する。
方針：cone の二射影で作用を計算し、第一成分の符号を照合する。
規約：任意次数の前合成を扱い、次数零の自然性だけで済ませない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の cone の代表可能性。
-/
theorem representableCone_naturality {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z)
    (x y : (CochainComplex C ℤ)ᵒᵖ) :
    (representableConeModule A f).map x y ≫
        homPostcompose _ (mappingConeComparison A y.unop f) =
      (representable A (mappingCone f)).map x y ≫
        homPrecompose (mappingConeComparison A x.unop f) _ := by
  apply closedFamily_of_action A (M := representableConeModule A f)
    (N := representable A (mappingCone f)) (fun t => mappingConeComparison A t.unop f) ?_ x y
  intro x y p r n hn a b
  let kx := mappingPostcompose A x.unop f
  let ky := mappingPostcompose A y.unop f
  let ay := (representableMap A Y x y).f p a
  let az := (representableMap A Z x y).f p a
  let α := (mappingCone.fst kx).val.v r (r + 1) rfl b
  let β := (mappingCone.snd kx).v r r (add_zero r) b
  let u := (coneMapCochain kx ky ay az).v r n hn b
  have hsign : p.negOnePow * (p * (r + 1)).negOnePow = (p * r).negOnePow := by
    rw [mul_add, mul_one, Int.negOnePow_add]
    calc
      p.negOnePow * ((p * r).negOnePow * p.negOnePow) =
          (p * r).negOnePow * (p.negOnePow * p.negOnePow) := by ac_rfl
      _ = (p * r).negOnePow := by rw [Int.units_mul_self, mul_one]
  have hf : (mappingCone.fst ky).val.v n (n + 1) rfl u =
      (p * r).negOnePow • a.comp α (by omega) := by
    have h := congrArg (fun g => g b) (coneMapCochain_fst_v kx ky ay az r n hn)
    change (mappingCone.fst ky).val.v n (n + 1) rfl u =
      p.negOnePow • (((representableMap A Y x y).f p a).v
        (r + 1) (n + 1) (by omega) α) at h
    rw [representableMap_apply, forward_cochain, smul_smul, hsign] at h
    exact h
  have hs : (mappingCone.snd ky).v n n (add_zero n) u =
      (p * r).negOnePow • a.comp β (by omega) := by
    have h := congrArg (fun g => g b) (coneMapCochain_snd_v kx ky ay az r n hn)
    change (mappingCone.snd ky).v n n (add_zero n) u =
      (((representableMap A Z x y).f p a).v r n hn β) at h
    rw [representableMap_apply, forward_cochain] at h
    exact h
  unfold moduleAction
  change (mappingConeComparison A y.unop f).f n u =
    (((representableMap A (mappingCone f) x y).f p a).v r n hn
      ((mappingConeComparison A x.unop f).f r b))
  rw [representableMap_apply, forward_cochain]
  change mappingCone.liftCochain f
      ((mappingCone.fst ky).val.v n (n + 1) rfl u)
      ((mappingCone.snd ky).v n n (add_zero n) u) rfl =
    (p * r).negOnePow • a.comp (mappingCone.liftCochain f α β rfl) (by omega)
  exact (congrArg₂ (fun c d => mappingCone.liftCochain f c d rfl) hf hs).trans
    ((coneLift_units_smul f n _ _ _).trans
      (congrArg ((p * r).negOnePow • ·) (comp_coneLift f a α β (by omega)).symm))

/--
概要：後合成の cone 加群は、元の複体の cone の代表加群と同型。
方針：全次数自然な写像複体の cone 同型を加群同型へ束ねる。
規約：同じ後合成射を cone に入れる。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
def representableConeIso {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    ForgetEnrichment.of (Complex A) (representableConeModule A f) ≅
      ForgetEnrichment.of (Complex A) (representable A (mappingCone f)) :=
  moduleIsoMk A (CochainComplex C ℤ) (fun x => mappingConeIso A x.unop f)
    (representableCone_naturality A f)

/--
概要：代表加群の実際の後合成射の標準 cone は、元の cone の代表加群と同型。
方針：標準 cone の評価成分を具体的な後合成の族へ同定し、同じ cone 比較へ渡す。
規約：別の射や別の cone を選ばない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の有限 cell の cone 閉性。
-/
def representableStandardConeIso {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    moduleCone A (CochainComplex C ℤ) (representablePostcompose A f) ≅
      ForgetEnrichment.of (Complex A) (representable A (mappingCone f)) := by
  let M := ForgetEnrichment.of (Complex A) (representable A Y)
  let N := ForgetEnrichment.of (Complex A) (representable A Z)
  let F := representablePostcompose A f
  let a := closedTransApp A (moduleClosedHomEquiv A (CochainComplex C ℤ) M N F)
  have ha := closedTransApp_naturality A (moduleClosedHomEquiv A (CochainComplex C ℤ) M N F)
  have hab : a = fun x : (CochainComplex C ℤ)ᵒᵖ => mappingPostcompose A x.unop f := by
    funext x
    change (moduleEvaluation A (CochainComplex C ℤ) x.unop).map
      (representablePostcompose A f) = mappingPostcompose A x.unop f
    exact representablePostcompose_eval A f x.unop
  have hc := coneModule_family_congr A ha (representablePostcompose_naturality A f) hab
  exact eqToIso (congrArg (fun P : RightModule A (CochainComplex C ℤ) =>
    ForgetEnrichment.of (Complex A) P) hc) ≪≫ representableConeIso A f

end SerrePositivity.KST.DerivedGeometry.LinearComplex
