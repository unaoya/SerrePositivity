module

public import SerrePositivity.DifferentialGraded.Module.Biproduct
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomology
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyLinear
public import SerrePositivity.DifferentialGraded.Derived.Linear
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import Mathlib.CategoryTheory.Types.Basic
public import SerrePositivity.DifferentialGraded.Complexes.CoproductHomologySupport
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Module.Colimits

/-!
# Perfect.RepresentableHomology

## 概要
8 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v

/-! ## FiniteCell（旧 SerrePositivity/DifferentialGraded/Perfect/FiniteCell.lean） -/

/-! # 指定生成元からの有限cellの構成データ

対象宇宙は縮小せず、有限操作の木と生成元への依存を保持する。
-/

@[expose] public section FiniteCell

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表加群から有限回の和・shift・cone・同型で作った証明付きcell。 -/
inductive ModuleFiniteCellCode (S : Set D) : ModuleCategory A D → Type (max (u + 1) v)
  | zero : ModuleFiniteCellCode S (moduleZero A D)
  | generator (x : D) (hx : x ∈ S) :
      ModuleFiniteCellCode S (ForgetEnrichment.of (Complex A) (representable A x))
  | shift {M : ModuleCategory A D} (s : ℤ) (c : ModuleFiniteCellCode S M) :
      ModuleFiniteCellCode S (M⟦s⟧)
  | sum {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M)
      (d : ModuleFiniteCellCode S N) : ModuleFiniteCellCode S (moduleBiprod A D M N)
  | cone {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M)
      (d : ModuleFiniteCellCode S N) (f : M ⟶ N) : ModuleFiniteCellCode S (moduleCone A D f)
  | iso {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M) (e : M ≅ N) :
      ModuleFiniteCellCode S N

namespace ModuleFiniteCellCode
variable {A D} {S T : Set D}

/-- 生成元の集合を大きくしても同じ有限操作の木を使える。 -/
def mono (h : S ⊆ T) {M : ModuleCategory A D} :
    ModuleFiniteCellCode A D S M → ModuleFiniteCellCode A D T M
  | .zero => .zero
  | .generator x hx => .generator x (h hx)
  | .shift s c => .shift s (c.mono h)
  | .sum c d => .sum (c.mono h) (d.mono h)
  | .cone c d f => .cone (c.mono h) (d.mono h) f
  | .iso c e => .iso (c.mono h) e

/-- 操作木に現れる節点数。任意の同型による輸送も一操作として数える。 -/
def size {M : ModuleCategory A D} : ModuleFiniteCellCode A D S M → ℕ
  | .zero => 1
  | .generator _ _ => 1
  | .shift _ c => c.size + 1
  | .sum c d => c.size + d.size + 1
  | .cone c d _ => c.size + d.size + 1
  | .iso c _ => c.size + 1

/-- 操作木に実際に現れる有限個の代表生成元。 -/
noncomputable def support {M : ModuleCategory A D} : ModuleFiniteCellCode A D S M → Finset D := by
  classical
  exact fun c => match c with
    | .zero => ∅
    | .generator x _ => {x}
    | .shift _ c => c.support
    | .sum c d => c.support ∪ d.support
    | .cone c d _ => c.support ∪ d.support
    | .iso c _ => c.support

lemma support_subset {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    (↑c.support : Set D) ⊆ S := by
  classical
  induction c with
  | zero => simp [support]
  | generator x hx => simpa only [support, Finset.coe_singleton, Set.singleton_subset_iff] using hx
  | shift s c ih => exact ih
  | sum c d ihc ihd =>
    simpa only [support, Finset.coe_union] using Set.union_subset ihc ihd
  | cone c d f ihc ihd =>
    simpa only [support, Finset.coe_union] using Set.union_subset ihc ihd
  | iso c e ih => exact ih

/-- 同じ対象を、操作木に現れる有限個の生成元だけで構成し直す。 -/
noncomputable def restrictSupport {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    ModuleFiniteCellCode A D (↑c.support : Set D) M := by
  classical
  induction c with
  | zero => exact .zero
  | generator x hx => exact .generator x (by simp [support])
  | shift s c ih => exact .shift s ih
  | sum c d ihc ihd =>
    exact .sum (ihc.mono (by intro x hx; exact Finset.mem_union_left _ hx))
      (ihd.mono (by intro x hx; exact Finset.mem_union_right _ hx))
  | cone c d f ihc ihd =>
    exact .cone (ihc.mono (by intro x hx; exact Finset.mem_union_left _ hx))
      (ihd.mono (by intro x hx; exact Finset.mem_union_right _ hx)) f
  | iso c e ih => exact .iso ih e

end ModuleFiniteCellCode

/-- 指定集合の代表加群から有限回の操作で構成できる性質。 -/
def moduleFiniteCellOver (S : Set D) : ObjectProperty (ModuleCategory A D) :=
  fun M => Nonempty (ModuleFiniteCellCode A D S M)

/-- すべての代表加群を生成元として許したfinite cell。 -/
def moduleFiniteCell : ObjectProperty (ModuleCategory A D) := moduleFiniteCellOver A D Set.univ

lemma moduleFiniteCellOver_mono {S T : Set D} (h : S ⊆ T) {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleFiniteCellOver A D T M := by
  obtain ⟨c⟩ := hM
  exact ⟨c.mono h⟩

/-- 各finite cellは有限個の指定生成元だけに依存する。 -/
lemma moduleFiniteCellOver_iff_finite_generators (S : Set D) (M : ModuleCategory A D) :
    moduleFiniteCellOver A D S M ↔ ∃ t : Finset D, (↑t : Set D) ⊆ S ∧
      moduleFiniteCellOver A D (↑t : Set D) M := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.support, c.support_subset, ⟨c.restrictSupport⟩⟩
  · rintro ⟨t, ht, hM⟩
    exact moduleFiniteCellOver_mono A D ht hM

lemma moduleFiniteCellOver_zero (S : Set D) : moduleFiniteCellOver A D S (moduleZero A D) :=
  ⟨.zero⟩

lemma moduleFiniteCellOver_representable {S : Set D} (x : D) (hx : x ∈ S) :
    moduleFiniteCellOver A D S (ForgetEnrichment.of (Complex A) (representable A x)) :=
  ⟨.generator x hx⟩

lemma moduleFiniteCellOver_shift {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (s : ℤ) : moduleFiniteCellOver A D S (M⟦s⟧) := by
  obtain ⟨c⟩ := hM
  exact ⟨.shift s c⟩

lemma moduleFiniteCellOver_biprod {S : Set D} {M N : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (hN : moduleFiniteCellOver A D S N) :
    moduleFiniteCellOver A D S (moduleBiprod A D M N) := by
  obtain ⟨c⟩ := hM
  obtain ⟨d⟩ := hN
  exact ⟨.sum c d⟩

lemma moduleFiniteCellOver_cone {S : Set D} {M N : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (hN : moduleFiniteCellOver A D S N) (f : M ⟶ N) :
    moduleFiniteCellOver A D S (moduleCone A D f) := by
  obtain ⟨c⟩ := hM
  obtain ⟨d⟩ := hN
  exact ⟨.cone c d f⟩

lemma moduleFiniteCellOver_of_iso {S : Set D} {M N : ModuleCategory A D}
    (e : M ≅ N) (hM : moduleFiniteCellOver A D S M) : moduleFiniteCellOver A D S N := by
  obtain ⟨c⟩ := hM
  exact ⟨.iso c e⟩

instance moduleFiniteCellOverClosedUnderIso (S : Set D) :
    (moduleFiniteCellOver A D S).IsClosedUnderIsomorphisms where
  of_iso := moduleFiniteCellOver_of_iso A D

lemma moduleFiniteCell_representable (x : D) :
    moduleFiniteCell A D (ForgetEnrichment.of (Complex A) (representable A x)) :=
  moduleFiniteCellOver_representable A D x (Set.mem_univ x)

lemma moduleFiniteCell_iff_finite_generators (M : ModuleCategory A D) :
    moduleFiniteCell A D M ↔ ∃ t : Finset D, moduleFiniteCellOver A D (↑t : Set D) M := by
  constructor
  · intro hM
    obtain ⟨t, _, ht⟩ := (moduleFiniteCellOver_iff_finite_generators A D Set.univ M).1 hM
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact moduleFiniteCellOver_mono A D (Set.subset_univ _) ht

end SerrePositivity.DifferentialGraded
end

end FiniteCell

/-! ## SmallStages（旧 SerrePositivity/DifferentialGraded/Perfect/SmallStages.lean） -/

/-! # 有限cellの小さい段階別代表族

各段階はType uの添字族で、前段階・整数shift・二項和・全ての閉零射のconeを列挙する。
同型による閉包は列挙せず、後で同型までの被覆を証明する。
-/

@[expose] public section SmallStages

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 小さい添字型と、その添字ごとの指定生成集合S上の有限cell。対象全体は縮小しない。 -/
def ModuleFiniteCellFamily (S : Set D) :=
  Σ I : Type u, I → {M : ModuleCategory A D // moduleFiniteCellOver A D S M}

/-- 第零段階は零対象とSの全代表加群。Sの対象宇宙のみをShrinkで縮める。 -/
def moduleFiniteCellFamilyZero (S : Set D) : ModuleFiniteCellFamily A D S :=
  ⟨PUnit.{u + 1} ⊕ Shrink.{u} S, fun i => match i with
    | .inl _ => ⟨moduleZero A D, moduleFiniteCellOver_zero A D S⟩
    | .inr j => let x := (equivShrink S).symm j
      ⟨ForgetEnrichment.of (Complex A) (representable A x.val),
        moduleFiniteCellOver_representable A D x.val x.property⟩⟩

/-- 一段階の拡張。coneの添字には実際の閉零加群射を使うので全てのconeを含む。 -/
def moduleFiniteCellFamilyNext {S : Set D} (F : ModuleFiniteCellFamily A D S) :
    ModuleFiniteCellFamily A D S :=
  ⟨F.1 ⊕ (ℤ × F.1) ⊕ (F.1 × F.1) ⊕
      (Σ i : F.1, Σ j : F.1, (F.2 i).val ⟶ (F.2 j).val), fun k => match k with
    | .inl i => F.2 i
    | .inr (.inl (s, i)) =>
      ⟨(F.2 i).val⟦s⟧, moduleFiniteCellOver_shift A D (F.2 i).property s⟩
    | .inr (.inr (.inl (i, j))) =>
      ⟨moduleBiprod A D (F.2 i).val (F.2 j).val,
        moduleFiniteCellOver_biprod A D (F.2 i).property (F.2 j).property⟩
    | .inr (.inr (.inr ⟨i, j, f⟩)) =>
      ⟨moduleCone A D f, moduleFiniteCellOver_cone A D (F.2 i).property (F.2 j).property f⟩⟩

/-- 有限操作の深さを自然数で制御した小さい代表族。 -/
def moduleFiniteCellStage (S : Set D) : ℕ → ModuleFiniteCellFamily A D S
  | 0 => moduleFiniteCellFamilyZero A D S
  | n + 1 => moduleFiniteCellFamilyNext A D (moduleFiniteCellStage S n)

/-- 前段階の添字は左の包含で次段階へ入り、表す対象は定義的に同じである。 -/
lemma moduleFiniteCellStage_succ (S : Set D) (n : ℕ)
    (i : (moduleFiniteCellStage A D S n).1) :
    ∃ j : (moduleFiniteCellStage A D S (n + 1)).1,
      (moduleFiniteCellStage A D S (n + 1)).2 j = (moduleFiniteCellStage A D S n).2 i :=
  ⟨Sum.inl i, rfl⟩

/-- 段階を大きくしても同じ有限cell代表を利用できる。二つの操作木の深さを揃えるために使う。 -/
lemma moduleFiniteCellStage_lift (S : Set D) {m n : ℕ} (h : m ≤ n)
    (i : (moduleFiniteCellStage A D S m).1) :
    ∃ j : (moduleFiniteCellStage A D S n).1,
      (moduleFiniteCellStage A D S n).2 j = (moduleFiniteCellStage A D S m).2 i := by
  induction h with
  | refl => exact ⟨i, rfl⟩
  | @step n h ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hk⟩ := moduleFiniteCellStage_succ A D S n j
    exact ⟨k, hk.trans hj⟩

/-- 全段階の添字はType uに留まる。Homの局所小性から対象の小ささを推論してはいない。 -/
abbrev ModuleFiniteCellStageIndex (S : Set D) := Σ n : ℕ, (moduleFiniteCellStage A D S n).1

/-- 全段階の小さい添字族から実際の閉零加群圏への評価。 -/
def moduleFiniteCellStageObject (S : Set D) (i : ModuleFiniteCellStageIndex A D S) :
    ModuleCategory A D := (moduleFiniteCellStage A D S i.1).2 i.2 |>.val

/-- 段階別代表は指定生成元からの有限cellである。 -/
lemma moduleFiniteCellStageObject_finite (S : Set D) (i : ModuleFiniteCellStageIndex A D S) :
    moduleFiniteCellOver A D S (moduleFiniteCellStageObject A D S i) :=
  ((moduleFiniteCellStage A D S i.1).2 i.2).property

end SerrePositivity.DifferentialGraded
end

end SmallStages

/-! ## SmallStageCover（旧 SerrePositivity/DifferentialGraded/Perfect/SmallStageCover.lean） -/

/-! # 有限cellの段階別代表による同型までの被覆

同型閉包自体を大きい対象型で列挙せず、構成木の帰納法で小さい代表へ移す。
-/

@[expose] public section SmallStageCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Arrow圏の同型を標準coneの同型へ送る。段階の添字から独立した型でcone関手を適用する。 -/
def moduleConeIsoOfArrowIso {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (e : Arrow.mk f ≅ Arrow.mk g) :
    moduleCone A D f ≅ moduleCone A D g :=
  (moduleConeFunctor A D).mapIso (X := Arrow.mk f) (Y := Arrow.mk g) e

/-- 二つの段階の対象を共通の段階へ運ぶ。和とconeの二つの枝に適用する。 -/
lemma moduleFiniteCellStage_pair {S : Set D} (m n : ℕ)
    (i : (moduleFiniteCellStage A D S m).1) (j : (moduleFiniteCellStage A D S n).1) :
    ∃ (k : ℕ) (i' j' : (moduleFiniteCellStage A D S k).1),
      (moduleFiniteCellStage A D S k).2 i' = (moduleFiniteCellStage A D S m).2 i ∧
      (moduleFiniteCellStage A D S k).2 j' = (moduleFiniteCellStage A D S n).2 j := by
  obtain ⟨i', hi⟩ := moduleFiniteCellStage_lift A D S (Nat.le_max_left m n) i
  obtain ⟨j', hj⟩ := moduleFiniteCellStage_lift A D S (Nat.le_max_right m n) j
  exact ⟨max m n, i', j', hi, hj⟩

/-- 有限cellの任意の構成木は、ある小さい段階の対象と厳密な加群同型で結ばれる。 -/
lemma ModuleFiniteCellCode.exists_stage {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    ∃ (n : ℕ) (i : (moduleFiniteCellStage A D S n).1),
      Nonempty (((moduleFiniteCellStage A D S n).2 i).val ≅ M) := by
  induction c with
  | zero => exact ⟨0, .inl PUnit.unit, ⟨Iso.refl _⟩⟩
  | generator x hx =>
    refine ⟨0, .inr (equivShrink S ⟨x, hx⟩), ?_⟩
    simp only [moduleFiniteCellStage, moduleFiniteCellFamilyZero, Equiv.symm_apply_apply]
    exact ⟨Iso.refl _⟩
  | shift s c ih =>
    obtain ⟨n, i, ⟨e⟩⟩ := ih
    exact ⟨n + 1, .inr (.inl (s, i)), ⟨(shiftFunctor _ s).mapIso e⟩⟩
  | @sum M N c d ihc ihd =>
    obtain ⟨m, i, ⟨eM⟩⟩ := ihc
    obtain ⟨n, j, ⟨eN⟩⟩ := ihd
    obtain ⟨k, i', j', hi, hj⟩ := moduleFiniteCellStage_pair A D m n i j
    have eM' : ((moduleFiniteCellStage A D S k).2 i').val ≅ M := by rw [hi]; exact eM
    have eN' : ((moduleFiniteCellStage A D S k).2 j').val ≅ N := by rw [hj]; exact eN
    refine ⟨k + 1, .inr (.inr (.inl (i', j'))), ?_⟩
    exact ⟨moduleBiprodIso A D _ _ ≪≫ biprod.mapIso eM' eN' ≪≫ (moduleBiprodIso A D M N).symm⟩
  | @cone M N c d f ihc ihd =>
    obtain ⟨m, i, ⟨eM⟩⟩ := ihc
    obtain ⟨n, j, ⟨eN⟩⟩ := ihd
    obtain ⟨k, i', j', hi, hj⟩ := moduleFiniteCellStage_pair A D m n i j
    have eM' : ((moduleFiniteCellStage A D S k).2 i').val ≅ M := by rw [hi]; exact eM
    have eN' : ((moduleFiniteCellStage A D S k).2 j').val ≅ N := by rw [hj]; exact eN
    let g := eM'.hom ≫ f ≫ eN'.inv
    refine ⟨k + 1, .inr (.inr (.inr ⟨i', j', g⟩)), ?_⟩
    have e : Arrow.mk g ≅ Arrow.mk f := Arrow.isoMk' g f eM' eN' (by simp [g])
    change Nonempty (moduleCone A D g ≅ moduleCone A D f)
    exact ⟨moduleConeIsoOfArrowIso A D g f e⟩
  | iso c e ih =>
    obtain ⟨n, i, ⟨e'⟩⟩ := ih
    exact ⟨n, i, ⟨e' ≪≫ e⟩⟩

/-- 指定生成集合のfinite cellは小さい段階別代表族で同型まで被覆される。 -/
lemma moduleFiniteCellOver_exists_stage {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    ∃ i : ModuleFiniteCellStageIndex A D S,
      Nonempty (moduleFiniteCellStageObject A D S i ≅ M) := by
  obtain ⟨c⟩ := hM
  obtain ⟨n, i, hi⟩ := c.exists_stage A D
  exact ⟨⟨n, i⟩, hi⟩

end SerrePositivity.DifferentialGraded
end

end SmallStageCover

/-! ## RepresentableHomology（旧 SerrePositivity/DifferentialGraded/Perfect/RepresentableHomology.lean） -/

/-! # 代表加群からの導来射と評価先の次数零ホモロジー -/

@[expose] public section RepresentableHomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全Hom endの次数零ホモロジーによる射影的始域の射計算。 -/
def moduleProjectiveDerivedHomologyEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) ≃
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)).homology 0 :=
  (moduleProjectiveDerivedHomEquiv A D hP N).symm.trans
    (homotopyHomologyEquiv A (RightModule A D) P N)

lemma moduleProjectiveDerivedHomologyEquiv_map {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (f : P ⟶ N) :
    moduleProjectiveDerivedHomologyEquiv A D hP N ((moduleToDerived A D).map f) =
      complexZeroHomologyClass A (homObject A (RightModule A D) P N)
        (closedHomEquiv A (RightModule A D) P N f) := by
  rw [← moduleProjectiveDerivedHomEquiv_map A D hP f]
  change homotopyHomologyEquiv A (RightModule A D) P N
    ((moduleProjectiveDerivedHomEquiv A D hP N).symm
      ((moduleProjectiveDerivedHomEquiv A D hP N) ((moduleToHomotopy A D).map f))) = _
  rw [Equiv.symm_apply_apply]
  exact homotopyHomologyEquiv_map A (RightModule A D) P N f

/-- dg Yonedaと実際の局所化Hom計算の合成。Hom_Dのflat性は不要。 -/
def moduleRepresentableDerivedHomologyEquiv (x : D) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) ≃
        ((ForgetEnrichment.to (Complex A) N).obj (op x)).homology 0 :=
  (moduleProjectiveDerivedHomologyEquiv A D (representable_homotopicallyProjective A D x) N).trans
    (HomologicalComplex.homologyMapIso
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)) 0).toLinearEquiv.toEquiv

lemma moduleRepresentableDerivedHomologyEquiv_map (x : D) {N : ModuleCategory A D}
    (f : ForgetEnrichment.of (Complex A) (representable A x) ⟶ N) :
    moduleRepresentableDerivedHomologyEquiv A D x N ((moduleToDerived A D).map f) =
      homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
        (complexZeroHomologyClass A
          (moduleHom A D (representable A x) (ForgetEnrichment.to (Complex A) N))
          (closedHomEquiv A (RightModule A D)
            (ForgetEnrichment.of (Complex A) (representable A x)) N f)) := by
  change homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
    (moduleProjectiveDerivedHomologyEquiv A D
      (representable_homotopicallyProjective A D x) N ((moduleToDerived A D).map f)) = _
  rw [moduleProjectiveDerivedHomologyEquiv_map]
  rfl

/-- 任意の主導来対象についての代表加群による評価ホモロジーの表示。 -/
def moduleRepresentableDerivedHomEquiv (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃
      (moduleDerivedHomology A D x 0).obj X := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableDerivedHomologyEquiv A D x N

lemma moduleRepresentableDerivedHomEquiv_obj (x : D) (N : ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    moduleRepresentableDerivedHomEquiv A D x ((moduleToDerived A D).obj N) f =
      moduleRepresentableDerivedHomologyEquiv A D x N f := rfl

end SerrePositivity.DifferentialGraded
end

end RepresentableHomology

/-! ## RepresentableHomologyLinear（旧 SerrePositivity/DifferentialGraded/Perfect/RepresentableHomologyLinear.lean） -/

/-! # 射影的始域・代表加群の導来Hom計算のA線形性 -/

@[expose] public section RepresentableHomologyLinear

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveDerivedHomEquiv_add {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D)
    (f g : (moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) :
    moduleProjectiveDerivedHomEquiv A D hP N (f + g) =
      moduleProjectiveDerivedHomEquiv A D hP N f + moduleProjectiveDerivedHomEquiv A D hP N g := by
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [← (moduleToHomotopy A D).map_add, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
    (moduleToDerived A D).map_add]

lemma moduleProjectiveDerivedHomEquiv_smul {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) (a : A)
    (f : (moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) :
    moduleProjectiveDerivedHomEquiv A D hP N (a • f) =
      a • moduleProjectiveDerivedHomEquiv A D hP N f := by
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  rw [← (moduleToHomotopy A D).map_smul, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, (moduleToDerived A D).map_smul]

def moduleProjectiveDerivedHomLinearEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) ≃ₗ[A]
      ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) where
  __ := moduleProjectiveDerivedHomEquiv A D hP N
  map_add' := moduleProjectiveDerivedHomEquiv_add A D hP N
  map_smul' := moduleProjectiveDerivedHomEquiv_smul A D hP N

def moduleProjectiveDerivedHomologyLinearEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) ≃ₗ[A]
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)).homology 0 :=
  (moduleProjectiveDerivedHomLinearEquiv A D hP N).symm.trans
    (homotopyHomologyLinearEquiv A (RightModule A D) P N)

def moduleRepresentableDerivedHomologyLinearEquiv (x : D) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) ≃ₗ[A]
        ((ForgetEnrichment.to (Complex A) N).obj (op x)).homology 0 :=
  (moduleProjectiveDerivedHomologyLinearEquiv A D
    (representable_homotopicallyProjective A D x) N).trans
    (HomologicalComplex.homologyMapIso
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)) 0).toLinearEquiv

def moduleRepresentableDerivedHomLinearEquiv (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃ₗ[A]
      (moduleDerivedHomology A D x 0).obj X := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableDerivedHomologyLinearEquiv A D x N

lemma moduleRepresentableDerivedHomLinearEquiv_toEquiv (x : D) (X : DerivedModuleCategory A D) :
    (moduleRepresentableDerivedHomLinearEquiv A D x X).toEquiv =
      moduleRepresentableDerivedHomEquiv A D x X := by
  obtain ⟨⟨N⟩⟩ := X
  rfl

end SerrePositivity.DifferentialGraded
end

end RepresentableHomologyLinear

/-! ## RepresentableHomologyNaturality（旧 SerrePositivity/DifferentialGraded/Perfect/RepresentableHomologyNaturality.lean） -/

/-! # 代表加群の導来Hom計算と後合成の自然性 -/

@[expose] public section RepresentableHomologyNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveDerivedHomologyEquiv_postcompose {P M N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P)
    (f : (moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj M) (g : M ⟶ N) :
    moduleProjectiveDerivedHomologyEquiv A D hP N (f ≫ (moduleToDerived A D).map g) =
      homologyMap (eHomWhiskerLeft (Complex A) P g) 0
        (moduleProjectiveDerivedHomologyEquiv A D hP M f) := by
  obtain ⟨f, rfl⟩ := moduleProjectiveToDerived_map_surjective A D hP f
  rw [← (moduleToDerived A D).map_comp, moduleProjectiveDerivedHomologyEquiv_map,
    moduleProjectiveDerivedHomologyEquiv_map, complexZeroHomologyClass_naturality,
    closedHomEquiv_postcompose]

lemma dgYonedaIso_postcompose (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f ≫
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom =
    (dgYonedaIso A x (ForgetEnrichment.to (Complex A) M)).hom ≫
      (moduleEvaluation A D x).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (yonedaEvaluateFamily A x (ForgetEnrichment.to (Complex A) N)
    (fun y => moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) N) y.unop)).f q
      ((eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f).f q z) =
    ((moduleEvaluation A D x).map f).f q
      ((yonedaEvaluateFamily A x (ForgetEnrichment.to (Complex A) M)
        (fun y => moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) M)
          y.unop)).f q z)
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  have hp : (moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) N) x).f q
      ((eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D) f).f q z) =
      ((moduleHomπ A D (representable A x) (ForgetEnrichment.to (Complex A) M) x).f q z).comp
        (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q) :=
    moduleHomWhiskerLeft_apply_π A D f q z x
  have hv := congrArg (fun k : Cochain ((representable A x).obj (op x))
      ((ForgetEnrichment.to (Complex A) N).obj (op x)) q =>
    k.v 0 q (by omega) (unitElement A x).val) hp
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply] at hv
  exact hv

lemma moduleRepresentableDerivedHomologyEquiv_postcompose (x : D) {M N : ModuleCategory A D}
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj M) (g : M ⟶ N) :
    moduleRepresentableDerivedHomologyEquiv A D x N (f ≫ (moduleToDerived A D).map g) =
      homologyMap ((moduleEvaluation A D x).map g) 0
        (moduleRepresentableDerivedHomologyEquiv A D x M f) := by
  change homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
    (moduleProjectiveDerivedHomologyEquiv A D
      (representable_homotopicallyProjective A D x) N (f ≫ (moduleToDerived A D).map g)) = _
  rw [moduleProjectiveDerivedHomologyEquiv_postcompose]
  have h := congrArg (fun k => homologyMap k 0) (dgYonedaIso_postcompose A D x g)
  simp only [homologyMap_comp] at h
  exact congrArg (fun k => k
    (moduleProjectiveDerivedHomologyEquiv A D (representable_homotopicallyProjective A D x) M f)) h

end SerrePositivity.DifferentialGraded
end

end RepresentableHomologyNaturality

/-! ## RepresentableHomologyNaturalIso（旧 SerrePositivity/DifferentialGraded/Perfect/RepresentableHomologyNaturalIso.lean） -/

/-! # 任意の導来射に自然な代表加群のHom計算

局所化の射宇宙へホモロジーの値をULiftし、局所化の普遍性で自然同型を延長する。
小さいHom宇宙や対象集合への置換は行わない。
-/

@[expose] public section RepresentableHomologyNaturalIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleRepresentableDerivedCoyoneda (x : D) :
    DerivedModuleCategory A D ⥤ Type (max (u + 1) v) :=
  coyoneda.obj (op ((moduleToDerived A D).obj
    (ForgetEnrichment.of (Complex A) (representable A x))))

def moduleDerivedHomologyLift (x : D) :
    DerivedModuleCategory A D ⥤ Type (max (u + 1) v) :=
  moduleDerivedHomology A D x 0 ⋙ forget (ModuleCat.{u} A) ⋙
    uliftFunctor.{max (u + 1) v, u}

def moduleRepresentableHomologyPreNatIso (x : D) :
    moduleToDerived A D ⋙ moduleRepresentableDerivedCoyoneda A D x ≅
      moduleToDerived A D ⋙ moduleDerivedHomologyLift A D x :=
  NatIso.ofComponents (fun N =>
    ((moduleRepresentableDerivedHomologyEquiv A D x N).trans Equiv.ulift.symm).toIso) (by
      intro M N g
      ext f
      have hg : (moduleDerivedHomology A D x 0).map ((moduleToDerived A D).map g) =
          HomologicalComplex.homologyMap ((moduleEvaluation A D x).map g) 0 := by
        exact eq_of_heq (Functor.hcongr_hom (moduleDerivedHomology_fac A D x 0) g)
      change ULift.up (moduleRepresentableDerivedHomologyEquiv A D x N
        (f ≫ (moduleToDerived A D).map g)) =
        ULift.up ((moduleDerivedHomology A D x 0).map ((moduleToDerived A D).map g)
          (moduleRepresentableDerivedHomologyEquiv A D x M f))
      rw [hg, moduleRepresentableDerivedHomologyEquiv_postcompose]
      rfl)

def moduleRepresentableHomologyNatIso (x : D) :
    moduleRepresentableDerivedCoyoneda A D x ≅ moduleDerivedHomologyLift A D x :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ moduleRepresentableDerivedCoyoneda A D x)
    (moduleToDerived A D ⋙ moduleDerivedHomologyLift A D x)
    (moduleRepresentableDerivedCoyoneda A D x) (moduleDerivedHomologyLift A D x)
    (moduleRepresentableHomologyPreNatIso A D x)

lemma moduleRepresentableHomologyNatIso_app_obj (x : D) (N : ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    (moduleRepresentableHomologyNatIso A D x).hom.app ((moduleToDerived A D).obj N) f =
      ULift.up (moduleRepresentableDerivedHomologyEquiv A D x N f) := by
  simp only [moduleRepresentableHomologyNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom]
  rfl

lemma moduleRepresentableHomologyNatIso_app (x : D) (X : DerivedModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    (moduleRepresentableHomologyNatIso A D x).hom.app X f =
      ULift.up (moduleRepresentableDerivedHomEquiv A D x X f) := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableHomologyNatIso_app_obj A D x N f

lemma moduleRepresentableDerivedHomEquiv_naturality (x : D)
    {X Y : DerivedModuleCategory A D} (g : X ⟶ Y)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomEquiv A D x Y (f ≫ g) =
      (moduleDerivedHomology A D x 0).map g (moduleRepresentableDerivedHomEquiv A D x X f) := by
  have h := congrArg (fun k => k f) ((moduleRepresentableHomologyNatIso A D x).hom.naturality g)
  change (moduleRepresentableHomologyNatIso A D x).hom.app Y (f ≫ g) =
    ULift.up ((moduleDerivedHomology A D x 0).map g
      ((moduleRepresentableHomologyNatIso A D x).hom.app X f).down) at h
  rw [moduleRepresentableHomologyNatIso_app, moduleRepresentableHomologyNatIso_app] at h
  exact congrArg ULift.down h

lemma moduleRepresentableDerivedHomLinearEquiv_naturality (x : D)
    {X Y : DerivedModuleCategory A D} (g : X ⟶ Y)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomLinearEquiv A D x Y (f ≫ g) =
      (moduleDerivedHomology A D x 0).map g
        (moduleRepresentableDerivedHomLinearEquiv A D x X f) :=
  moduleRepresentableDerivedHomEquiv_naturality A D x g f

end SerrePositivity.DifferentialGraded
end

end RepresentableHomologyNaturalIso

/-! ## RepresentableCoproductSupport（旧 SerrePositivity/DifferentialGraded/Perfect/RepresentableCoproductSupport.lean） -/

/-! # 代表加群からの導来射の余積における有限support -/

@[expose] public section RepresentableCoproductSupport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主局所化での余積包含に沿う有限support表示。
族が射影的ならこのcofanは主導来圏の実際の余積である。 -/
lemma moduleRepresentableDerivedCoproduct_rep {J : Type u} (x : D)
    (M : J → ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj (∐ M)) :
    ∃ (t : Finset J)
      (g : ∀ j, (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ (moduleToDerived A D).obj (M j)),
      ∑ j ∈ t, g j ≫ (moduleToDerived A D).map (Sigma.ι M j) = f := by
  classical
  let E := moduleEvaluation A D x
  let s : Cofan (fun j => E.obj (M j)) :=
    Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hs : IsColimit s := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, c, hc⟩ := complexCofan_zeroHomology_rep A (fun j => E.obj (M j)) s hs
    (moduleRepresentableDerivedHomologyEquiv A D x (∐ M) f)
  let g := fun j => (moduleRepresentableDerivedHomologyEquiv A D x (M j)).symm (c j)
  refine ⟨t, g, ?_⟩
  apply (moduleRepresentableDerivedHomologyEquiv A D x (∐ M)).injective
  calc
    _ = ∑ j ∈ t, moduleRepresentableDerivedHomologyEquiv A D x (∐ M)
        (g j ≫ (moduleToDerived A D).map (Sigma.ι M j)) :=
      map_sum (moduleRepresentableDerivedHomologyLinearEquiv A D x (∐ M)).toLinearMap _ _
    _ = ∑ j ∈ t, homologyMap (s.inj j) 0 (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [moduleRepresentableDerivedHomologyEquiv_postcompose]
      change homologyMap (s.inj j) 0
        ((moduleRepresentableDerivedHomologyEquiv A D x (M j))
          ((moduleRepresentableDerivedHomologyEquiv A D x (M j)).symm (c j))) = _
      rw [Equiv.apply_symm_apply]
    _ = _ := hc

end SerrePositivity.DifferentialGraded
end

end RepresentableCoproductSupport
