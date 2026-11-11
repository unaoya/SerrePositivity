module
public import SerrePositivity.KST.SConstruction.ArCofiberInputs
public import SerrePositivity.KST.SConstruction.PointwiseCofiberFamilies

/-! # Ar[n] 上の cofiber 族の相対補完
概要：零対角の枠を入力として、既存の gapped 境界の cofiber 族を相対的に補完する。
方針：Ar[n] をパラメーターとする内部 Hom の trivial Kan fibration で持ち上げる。
規約：出力図式の gapped 条件と第一行の回収は別に証明する。
使われ方：第一行制限の全境界持ち上げの cofiber 段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：枠を入力とし、指定した gapped 境界を保つ Ar[n] 上の cofiber 族。
方針：族と入力・境界の二つの厳密な等号を保持する。
規約：補完後の図式の gapped 性はフィールドに仮定しない。
使われ方：第一行復元の cofiber 補完の証明データ。 -/
structure ArCofiberCompletion {A B C : SSet.{u}} (n : ℕ) (i : A ⟶ B)
    (a : A ⟶ sConstruction n C) (b : B ⟶ zeroFrameDiagrams n C) where
  family : B ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C)
  boundary : i ≫ family = a ≫ gappedCofiberFamiliesMap n C
  input : family ≫ (ihom (arNerve n)).map (cofiberProjection C) = b ≫ frameCofiberInputs n C

/-- 概要：枠の族は既存の gapped 境界の cofiber 族を保って補完できる。
方針：入力の可換式と内部 Hom の後合成の trivial Kan fibration を使う。
規約：i は任意の単射、C は安定な quasicategory。
使われ方：境界を固定した Ar[n] 全体への cofiber 補完。 -/
def arCofiberCompletion {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (n : ℕ) (i : A ⟶ B) [Mono i] (a : A ⟶ sConstruction n C)
    (b : B ⟶ zeroFrameDiagrams n C) (h : a ≫ gappedFrameRestriction n C = i ≫ b) :
    ArCofiberCompletion n i a b := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((ihom (arNerve n)).map (cofiberProjection C)) := inferInstance
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (ihom (arNerve n)).map (cofiberProjection C)) i inferInstance
  have sq : CommSq (a ≫ gappedCofiberFamiliesMap n C) i
      ((ihom (arNerve n)).map (cofiberProjection C)) (b ≫ frameCofiberInputs n C) := by
    constructor
    rw [Category.assoc, gappedCofiberFamiliesMap_input, ← Category.assoc, h, Category.assoc]
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：補完した cofiber 族の右上角を取って Ar[n] の図式の族にする。
方針：内部 Hom の後合成で右上角を評価する。
規約：この段階で gapped 性を主張しない。使われ方：完成した S_n の持ち上げの候補。 -/
def ArCofiberCompletion.diagram {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b) : B ⟶ (ihom (arNerve n)).obj C :=
  c.family ≫ (ihom (arNerve n)).map (cofiberApex C)

/-- 概要：補完した図式の族は指定した gapped 境界と厳密に一致する。
方針：cofiber 族の境界の等号と右上角の厳密な回収を合わせる。
規約：高次パラメーターも保持する。使われ方：第一行制限の相対境界条件。 -/
lemma ArCofiberCompletion.diagram_boundary {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b) : i ≫ c.diagram = a ≫ (gappedSubcomplex n C).ι := by
  rw [ArCofiberCompletion.diagram, ← Category.assoc, c.boundary,
    Category.assoc, gappedCofiberFamiliesMap_apex]

/-- 概要：補完した族をパラメーターの一頂点で評価して Ar[n] 上の cofiber 族にする。
方針：内部 Hom の頂点同値を逆に使う。
規約：選択は追加しない。使われ方：出力図式の gapped 条件の点ごとの検証。 -/
def ArCofiberCompletion.pointFamily {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b) (v : B _⦋0⦌) : arNerve n ⟶ cofiberDiagrams C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm (c.family.app (Opposite.op ⦋0⦌) v)

/-- 概要：補完した各 Ar[n] 上の cofiber 族は関手 ∞ 圏の cofiber 列を与える。
方針：族の点ごとの余極限の関手圏への移送を使う。
規約：C の quasicategory 性のみ。使われ方：全四角形の押し出し性への接続。 -/
lemma ArCofiberCompletion.pointFamily_isCofiber {A B C : SSet.{u}} [Quasicategory C]
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b) (v : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (cofiberFamilyTriangle (c.pointFamily v)) := cofiberFamilyTriangle_isCofiber _

end SerrePositivity.KST.SConstruction
