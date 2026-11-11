module
public import SerrePositivity.KST.SConstruction.ArCofiberFamiliesMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-! # Ar[n] 上の cofiber の入力の族
概要：零対角の枠から (0,i)→(0,j) の全ての射を自然に取り出す。
方針：Ar[n] と区間の積から第一行への順序写像を使う。
規約：入力は枠だけで定まる。使われ方：第一行からの cofiber 補完の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：区間 (i,j) に対する第一行の射の端点を返す順序写像。
方針：左端零の区間 (0,i)→(0,j) を取る。
規約：対角を含む枠の値。使われ方：cofiber の入力の族。 -/
def arCofiberInputOrder (n : ℕ) : Ar.{u} n × ULift.{u} (Fin 2) →o FrameAr.{u} n where
  toFun p := ⟨arObj 0 (intervalStep p.1.down.val.1 p.1.down.val.2 p.1.down.property p.2.down)
    (Fin.zero_le _), Or.inl rfl⟩
  monotone' a b h := by
    constructor
    · exact le_rfl
    · exact ((intervalStep a.1.down.val.1 a.1.down.val.2 a.1.down.property).monotone h.2).trans
        (intervalStep_mono_endpoints _ _ h.1.1 h.1.2 _)

/-- 概要：Ar[n] 上の全第一行の射を表す単体集合の添字写像。
方針：二つの鎖を同じ頂点番号で評価して順序写像を適用する。
規約：Ar[n] が第一因子。使われ方：cofiber の入力の自然性。 -/
def arCofiberInputMap (n : ℕ) : arNerve.{u} n ⊗ Δ[1] ⟶ frameNerve n where
  app d := ↾fun s ↦ (show Monotone (fun r : Fin (d.unop.len + 1) ↦
    arCofiberInputOrder n (s.1.obj r, ULift.up (stdSimplex.asOrderHom s.2 r))) from by
      intro r t h
      exact (arCofiberInputOrder n).monotone ⟨s.1.monotone h, (stdSimplex.asOrderHom s.2).monotone h⟩).functor
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    rfl

/-- 概要：cofiber 四角形の下辺の添字は枠から定まる第一行の射。
方針：鎖の各頂点で正方形の縦座標を零にする。
規約：厳密な形状の等号。使われ方：補完すべき入力の境界の照合。 -/
lemma arCofiberSquareMap_bottom (n : ℕ) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ arCofiberSquareMap.{u} n =
      arCofiberInputMap n ≫ frameInclusion n := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- 概要：枠の図式から全区間の cofiber の入力の族を抽出する作用素。
方針：入力の添字写像で前合成して内部 currying を使う。
規約：零対角条件を課す前でも定義できる。使われ方：相対 cofiber 補完の基底の構成。 -/
def frameCofiberInputOperator (n : ℕ) (C : SSet.{u}) :
    (ihom (frameNerve n)).obj C ⟶ (ihom (arNerve n)).obj ((ihom (Δ[1] : SSet.{u})).obj C) :=
  (pre ((β_ (Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberInputMap n)).app C ≫
    (ihomCurryIso (Δ[1] : SSet.{u}) (arNerve n) C).hom

/-- 概要：零対角の枠から全 cofiber 入力の族を抽出する。
方針：枠の図式の条件を忘れて入力の作用素を適用する。
規約：Ar[n] の全パラメーターに自然。使われ方：gapped 図式の復元の入力。 -/
def frameCofiberInputs (n : ℕ) (C : SSet.{u}) :
    zeroFrameDiagrams n C ⟶ (ihom (arNerve n)).obj ((ihom (Δ[1] : SSet.{u})).obj C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ frameCofiberInputOperator n C

/-- 概要：自然な cofiber 四角形の入力は枠から抽出した第一行の射と一致する。
方針：内部 currying の前合成に関する自然性と下辺の添字の等号を使う。
規約：全次数で厳密な等号。使われ方：相対 cofiber 補完の可換正方形。 -/
lemma arCofiberFamilyOperator_input (n : ℕ) (C : SSet.{u}) :
    arCofiberFamilyOperator n C ≫ (ihom (arNerve n)).map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C) =
      (pre (frameInclusion n)).app C ≫ frameCofiberInputOperator n C := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ▷ arNerve n ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom) ≫ arCofiberSquareMap n =
      ((β_ (Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberInputMap n) ≫ frameInclusion n := by
    rw [BraidedCategory.braiding_naturality_left, Category.assoc,
      arCofiberSquareMap_bottom, ← Category.assoc]
  dsimp only [arCofiberFamilyOperator, frameCofiberInputOperator]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ihomCurry_pre_whiskerRight]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rw [he]

/-- 概要：gapped 図式を枠へ制限して含めると通常の前合成。
方針：全部分複体の持ち上げを展開する。
規約：厳密等号。使われ方：抽出した cofiber の入力の境界。 -/
lemma gappedFrameRestriction_ι (n : ℕ) (C : SSet.{u}) :
    gappedFrameRestriction n C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι =
      (gappedSubcomplex n C).ι ≫ (pre (frameInclusion n)).app C := rfl

/-- 概要：gapped 図式の cofiber 族の入力は零対角の枠だけで定まる。
方針：cofiber の包含後の式と入力作用素の自然性を合わせる。
規約：全てのパラメーターに厳密に自然。使われ方：Ar[n] 全体への相対 cofiber 補完。 -/
lemma gappedCofiberFamiliesMap_input (n : ℕ) (C : SSet.{u}) :
    gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberProjection C) =
      gappedFrameRestriction n C ≫ frameCofiberInputs n C := by
  have hframe : gappedFrameRestriction n C ≫ frameCofiberInputs n C =
      (gappedSubcomplex n C).ι ≫ (pre (frameInclusion n)).app C ≫ frameCofiberInputOperator n C := by
    change (gappedFrameRestriction n C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι) ≫
      frameCofiberInputOperator n C = _
    rw [gappedFrameRestriction_ι, Category.assoc]
  rw [hframe, cofiberProjection, Functor.map_comp, ← Category.assoc, gappedCofiberFamiliesMap_ι,
    Category.assoc, arCofiberFamilyOperator_input]

end SerrePositivity.KST.SConstruction
