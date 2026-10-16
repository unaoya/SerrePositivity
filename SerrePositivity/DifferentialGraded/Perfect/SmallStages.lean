module
public import SerrePositivity.DifferentialGraded.Perfect.FiniteCell

/-! # 有限cellの小さい段階別代表族

各段階はType uの添字族で、前段階・整数shift・二項和・全ての閉零射のconeを列挙する。
同型による閉包は列挙せず、後で同型までの被覆を証明する。
-/
@[expose] public section
noncomputable section
universe u v
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
