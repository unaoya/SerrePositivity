module
public import SerrePositivity.KST.SConstruction.StructureMapCofibers

/-! # 零対象と cofiber を保つ射
概要：反復 S 構成に使う零対象と cofiber の保存条件を束ねる。
方針：gapped の標準 cofiber 判定と、Ar の各点での cofiber 判定を使う。
規約：既存の全押し出し保存条件を変更しない。使われ方：反復 S• の構造射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象と cofiber 正方形を保つ条件。
方針：零頂点と零角つきの普遍四角形を量化する。
規約：任意の押し出しの保存との同値はここでは主張しない。
使われ方：反復 S• の後合成の入力条件。 -/
def PreservesCofiberData {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  (∀ z : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z → _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app (Opposite.op ⦋0⦌) z)) ∧
    (∀ t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ f))

/-- 概要：全押し出しと零対象の保存は cofiber の保存条件を与える。
方針：零角つき正方形に保存条件を制限する。
規約：既存の条件を弱めて置換しない。使われ方：従来の後合成との比較。 -/
lemma PreservesSConstructionData.toCofiberData {C D : SSet.{u}} {f : C ⟶ D}
    (hf : PreservesSConstructionData f) : PreservesCofiberData f :=
  ⟨hf.1, fun t ht => hf.2 t.square ht⟩

/-- 概要：恒等射は零対象と cofiber を保存する。
方針：正方形を変えないことを使う。
規約：quasicategory 性は不要。使われ方：反復の恒等法則。 -/
lemma preservesCofiberData_id (C : SSet.{u}) : PreservesCofiberData (𝟙 C) := by
  constructor
  · intro z hz
    exact hz
  · intro t ht
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square at ht
    simpa only [Category.comp_id] using ht

/-- 概要：零対象と cofiber の保存条件は合成で閉じる。
方針：零角を保存してから cofiber 保存を二回適用する。
規約：追加の存在条件なし。使われ方：反復の合成法則。 -/
lemma PreservesCofiberData.comp {C D E : SSet.{u}} {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesCofiberData f) (hg : PreservesCofiberData g) : PreservesCofiberData (f ≫ g) := by
  constructor
  · intro z hz
    exact hg.1 _ (hf.1 z hz)
  · intro t ht
    let T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle D := ⟨t.square ≫ f, hf.1 _ t.zero_corner⟩
    exact hg.2 T (hf.2 t ht)

/-- 概要：零対象と cofiber を保つ射の後合成は全 gapped 条件を保存する。
方針：標準 cofiber 正方形の判定を用いて全四つ組の押し出しを回収する。
規約：gapped 条件を変更しない。使われ方：同じ S_n 上の後合成。 -/
lemma IsGapped.postcomp_of_cofiber {n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    {F : arNerve n ⟶ C} (hF : IsGapped F) (f : C ⟶ D) (hf : PreservesCofiberData f) :
    IsGapped (F ≫ f) := by
  apply (isGapped_iff_originSquares _).2
  constructor
  · intro i
    exact hf.1 _ (hF.1 i)
  · intro i j hij
    let T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C := ⟨arSquare 0 i i j (Fin.zero_le _) le_rfl hij ≫ F, hF.1 i⟩
    exact hf.2 T (hF.2 0 i i j (Fin.zero_le _) le_rfl hij)

/-- 概要：cofiber 保存条件から同じ全 gapped S_n の後合成を構成する。
方針：内部 Hom の後合成を gapped の全部分複体へ持ち上げる。
規約：全 gapped 図式を保持する。使われ方：S 構成の反復。 -/
def sPostcompCofiber (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) : sConstruction n C ⟶ sConstruction n D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f) (by
    intro v
    let F := gappedDiagram v
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm
      (((ihom (arNerve n)).map f).app (Opposite.op ⦋0⦌) v.val))
    rw [← hv]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D) (F ≫ f)))
    rw [Equiv.symm_apply_apply]
    exact IsGapped.postcomp_of_cofiber (gappedDiagram_isGapped v) f hf)

/-- 概要：cofiber 保存条件による後合成を含めると通常の後合成。
方針：全部分複体の持ち上げの式。
規約：全単体での厳密な等号。使われ方：関手法則の反映。 -/
lemma sPostcompCofiber_ι (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber n f hf ≫ (gappedSubcomplex n D).ι =
      (gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f := rfl

/-- 概要：従来の保存条件から作る後合成と新しい条件から作る後合成は一致する。
方針：同じ内部 Hom の写像の全部分複体への持ち上げであることを使う。
規約：等号は厳密。使われ方：既存の K 空間の関手性との接続。 -/
lemma sPostcompCofiber_eq_sPostcomp (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sPostcompCofiber n f (PreservesSConstructionData.toCofiberData hf) = sPostcomp n f hf := rfl

/-- 概要：cofiber 保存条件から作る後合成と評価は可換。
方針：包含後の式と内部 Hom の評価の自然性を使う。
規約：全次数での等号。使われ方：cofiber 保存の点ごとの判定。 -/
lemma sPostcompCofiber_gapped_evaluate (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (a : (arNerve n) _⦋0⦌) :
    sPostcompCofiber n f hf ≫ (gappedSubcomplex n D).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a ≫ f := by
  rw [← Category.assoc, sPostcompCofiber_ι, Category.assoc, ihom_postcomp_evaluate]

/-- 概要：cofiber 保存条件による S_n の後合成も零対象を保つ。
方針：定値零図式の像を直接計算して全零対象へ移す。
規約：chosen zero の一致は不要。使われ方：反復の零角。 -/
lemma sPostcompCofiber_isZeroVertex {n : ℕ} {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f)
    {v : (sConstruction n C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) v) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  apply map_isZeroVertex_of_zero_image (sPostcompCofiber n f hf)
    (sConstructionZeroVertex n z.vertex z.isZero) (sConstructionZeroVertex_isZero n _ _) _ hv
  have he : (sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌)
      (sConstructionZeroVertex n z.vertex z.isZero) =
      sConstructionZeroVertex n (f.app (Opposite.op ⦋0⦌) z.vertex) (hf.1 _ z.isZero) := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.const z.vertex : arNerve n ⟶ C) ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (f.app (Opposite.op ⦋0⦌) z.vertex))
    rw [SSet.const_comp]
  rw [he]
  exact sConstructionZeroVertex_isZero n _ _

/-- 概要：cofiber 保存条件による S_n の後合成は再び同じ保存条件を満たす。
方針：零対象の保存と Ar の全点での cofiber の判定を合わせる。
規約：両端は安定な quasicategory。使われ方：任意の有限反復。 -/
lemma preservesCofiberData_sPostcompCofiber (n : ℕ) {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    PreservesCofiberData (sPostcompCofiber n f hf) := by
  refine ⟨fun z hz => sPostcompCofiber_isZeroVertex f hf hz, ?_⟩
  intro t ht
  let T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n D) :=
    ⟨t.square ≫ sPostcompCofiber n f hf, sPostcompCofiber_isZeroVertex f hf t.zero_corner⟩
  apply (gappedInclusion_cofiber_iff_pointwise T).2
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((t.square ≫ sPostcompCofiber n f hf) ≫
    (gappedSubcomplex n D).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  rw [Category.assoc, sPostcompCofiber_gapped_evaluate, ← Category.assoc, ← Category.assoc]
  let A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C := ⟨t.square ≫ (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a,
    isZeroVertex_evaluateFunctorAt (gappedInclusion_isZeroVertex n t.zero_corner) a⟩
  exact hf.2 A ((gappedInclusion_cofiber_iff_pointwise t).1 ht a)

/-- 概要：S_n の単体作用は零対象と cofiber の保存条件を満たす。
方針：零対象保存と既に証明した cofiber 保存を合わせる。
規約：C は安定。使われ方：内側の添字の反復的な作用。 -/
lemma preservesCofiberData_sMap {m n : ℕ} (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (θ : Fin (m + 1) →o Fin (n + 1)) : PreservesCofiberData (sMap C θ) :=
  ⟨fun _z hz => sMap_isZeroVertex θ hz, fun t ht => sMap_preserves_cofiber θ t ht⟩

end SerrePositivity.KST.SConstruction
