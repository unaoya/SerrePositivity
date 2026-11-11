module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceCoproduct

/-! # 零始点の押し出しと標準二項余積の比較

概要：幾何学的な二項余積を Mathlib の選ばれた余積と比較し、二つの射影を作る。
方針：二項余錐の普遍性と零射を使う。
規約：前加法構造は不要。使われ方：包含の cofiber 列と積への標準比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：選ばれた二項余積は始対象始点の押し出しの終端頂点と同型である。
方針：二つの普遍二項余錐の一意性を使う。
規約：値域は quasicategory、安定性は不要。使われ方：標準包含との照合。 -/
def zeroSourcePushoutCoproductIso {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0))
    [HasBinaryCoproduct (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1)] :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0) ⨿ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1) ≅ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 1 :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz)

/-- 概要：比較同型は標準第一包含を四角形の右辺に送る。
方針：余極限の一意同型の第一脚の式。
規約：始点と終点を厳密に固定。使われ方：第一包含の cofiber 列。 -/
lemma zeroSourcePushoutCoproductIso_inl {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0))
    [HasBinaryCoproduct (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1)] :
    coprod.inl ≫ (zeroSourcePushoutCoproductIso R hR hz).hom = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R :=
  (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) ⟨WalkingPair.left⟩

/-- 概要：比較同型は標準第二包含を四角形の上辺に送る。
方針：余極限の一意同型の第二脚の式。
規約：始点と終点を厳密に固定。使われ方：第二包含と射影。 -/
lemma zeroSourcePushoutCoproductIso_inr {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0))
    [HasBinaryCoproduct (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1)] :
    coprod.inr ≫ (zeroSourcePushoutCoproductIso R hR hz).hom = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop R :=
  (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) ⟨WalkingPair.right⟩

/-- 概要：幾何学的二項余積から第一入力への射影。
方針：第一包含上で恒等、第二包含上で零となる降下射を取る。
規約：零射だけを仮定し、加法は使わない。使われ方：積への標準比較。 -/
def zeroSourceCoproductFst {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0 :=
  BinaryCofan.IsColimit.desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) (𝟙 _) 0

/-- 概要：幾何学的二項余積から第二入力への射影。
方針：第一包含上で零、第二包含上で恒等となる降下射を取る。
規約：零射だけを仮定し、加法は使わない。使われ方：包含の cofiber の射影との比較。 -/
def zeroSourceCoproductSnd {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 :=
  BinaryCofan.IsColimit.desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) 0 (𝟙 _)

/-- 概要：第一包含と第一射影の合成は恒等。
方針：降下射の第一脚の式。規約：零射のみを仮定。使われ方：第一包含の分裂性。 -/
lemma zeroSourceCoproduct_right_fst {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R ≫ zeroSourceCoproductFst R hR hz = 𝟙 _ :=
  BinaryCofan.IsColimit.inl_desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) _ _

/-- 概要：第二包含と第一射影の合成は零。
方針：降下射の第二脚の式。規約：零射のみを仮定。使われ方：双積の交差零合成。 -/
lemma zeroSourceCoproduct_top_fst {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop R ≫ zeroSourceCoproductFst R hR hz = 0 :=
  BinaryCofan.IsColimit.inr_desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) _ _

/-- 概要：第一包含と第二射影の合成は零。
方針：降下射の第一脚の式。規約：零射のみを仮定。使われ方：包含の cofiber との比較。 -/
lemma zeroSourceCoproduct_right_snd {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R ≫ zeroSourceCoproductSnd R hR hz = 0 :=
  BinaryCofan.IsColimit.inl_desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) _ _

/-- 概要：第二包含と第二射影の合成は恒等。
方針：降下射の第二脚の式。規約：零射のみを仮定。使われ方：第二包含の分裂性。 -/
lemma zeroSourceCoproduct_top_snd {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop R ≫ zeroSourceCoproductSnd R hR hz = 𝟙 _ :=
  BinaryCofan.IsColimit.inr_desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz) _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
