module
public import SerrePositivity.KST.SConstruction.Cofinality.CutKZeroAdditivity
public import SerrePositivity.KST.SConstruction.CutIntervalEquivalences

/-!
概要：区間の包含と収縮による K₀ の写像を保持する。
方針：元の端点制限を完全射に束ね、K₀ の合成則へ写す。
規約：K 理論の写像を選び直さず、全高次の元の S 制限を使う。
使われ方：障害余核の区間分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の区間制限を完全射として使う。
方針：既存の cofiber 保存証拠を添える。
規約：端点順序写像をそのまま使う。
使われ方：K₀ における制限と延長の共通表記。 -/
def cofinalitySRestriction {m n : ℕ} (X : StableModel.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) : sStableModel n X ⟶ sStableModel m X :=
  ⟨sMap X.carrier θ, preservesCofiberData_sMap X.carrier θ⟩

/-- 概要：元の S 制限は端点写像の合成を反変に保つ。
方針：元の単体的射の合成公式で完全射の等号を示す。
規約：証拠の違いは部分型の等号で除く。
使われ方：K₀ の厳密な区間計算。 -/
lemma cofinalitySRestriction_comp {l m n : ℕ} (X : StableModel.{u})
    (θ : Fin (l + 1) →o Fin (m + 1)) (φ : Fin (m + 1) →o Fin (n + 1)) :
    cofinalitySRestriction X (φ.comp θ) =
      cofinalitySRestriction X φ ≫ cofinalitySRestriction X θ :=
  Subtype.ext (sMap_comp X.carrier θ φ)

/-- 概要：元の区間制限の K₀ 作用。
方針：同じ完全射の三角圏 K₀ への作用を使う。
規約：S_n の対象類を保つ。
使われ方：障害余核の元の面写像の計算。 -/
def cutKZeroRestriction {m n : ℕ} (X : StableModel.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier) →+
      TriangulatedK0 (hoFunctor.obj (sStableModel m X).carrier) :=
  triangulatedKZeroSourceMap (cofinalitySRestriction X θ)

/-- 概要：端点制限の K₀ 作用の合成公式。
方針：元の S 制限と三角圏 K₀ の合成則を結ぶ。
規約：順序は元の反変な S 方向。
使われ方：区間の切断の二重評価。 -/
lemma cutKZeroRestriction_comp {l m n : ℕ} (X : StableModel.{u})
    (θ : Fin (l + 1) →o Fin (m + 1)) (φ : Fin (m + 1) →o Fin (n + 1)) :
    cutKZeroRestriction X (φ.comp θ) =
      (cutKZeroRestriction X θ).comp (cutKZeroRestriction X φ) :=
  (congrArg triangulatedKZeroSourceMap (cofinalitySRestriction_comp X θ φ)).trans
    (triangulatedKZeroSourceMap_comp _ _)

/-- 概要：恒等の区間制限は K₀ で恒等。
方針：元の sMap の恒等則を使う。
規約：同じ安定模型上の等号。
使われ方：左右の短い区間の回収。 -/
lemma cutKZeroRestriction_id (n : ℕ) (X : StableModel.{u}) :
    cutKZeroRestriction X (OrderHom.id : Fin (n + 1) →o _) = AddMonoidHom.id _ := by
  have he : cofinalitySRestriction X (OrderHom.id : Fin (n + 1) →o _) =
      𝟙 (sStableModel n X) := Subtype.ext (sMap_id n X.carrier)
  exact (congrArg triangulatedKZeroSourceMap he).trans (triangulatedKZeroSourceMap_id _)

/-- 概要：元の切断射は K₀ 上でも左右の端点制限として計算できる。
方針：切断の全角評価を完全射の等号へ写す。
規約：二つの角を別の延長関手で代用しない。
使われ方：短い区間への制限との照合。 -/
lemma cutKZero_corner (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (x y : Fin 2) :
    triangulatedKZeroSourceMap (cutStableComparison n k X ≫
      cofiberStableEvaluation (sStableModel n X)
        (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) =
      cutKZeroRestriction X (cutCornerOrder k x y) :=
  congrArg triangulatedKZeroSourceMap (cutStableComparison_evaluation n k X x y)

/-- 概要：左右の短い区間の制限後の延長の和は K₀ で恒等。
方針：元の切断の二角を区間の包含と収縮の合成へ書き換える。
規約：元の K₀ 上の等号であり、弱同値の仮定を入れない。
使われ方：余核の Segal 分解の逆写像。 -/
lemma cutKZero_interval_decomposition (n : ℕ) (k : Fin (n + 1))
    (X : StableModel.{u}) :
    AddMonoidHom.id (TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier)) =
      (cutKZeroRestriction X (cutLeftIntervalRetraction n k)).comp
        (cutKZeroRestriction X (cutLeftIntervalInclusion n k)) +
      (cutKZeroRestriction X (cutRightIntervalRetraction n k)).comp
        (cutKZeroRestriction X (cutRightIntervalInclusion n k)) := by
  have h := cutKZero_id n k X
  have hl := cutKZero_corner n k X 0 0
  have hr := cutKZero_corner n k X 1 1
  have el := (congrArg (cutKZeroRestriction X)
    (cutLeftInterval_inclusion_retraction n k).symm).trans
      (cutKZeroRestriction_comp X _ _)
  have er := (congrArg (cutKZeroRestriction X)
    (cutRightInterval_inclusion_retraction n k).symm).trans
      (cutKZeroRestriction_comp X _ _)
  exact h.trans (congrArg₂ (· + ·) (hl.trans el) (hr.trans er))

/-- 概要：左右の元の短い区間制限は K₀ の元を共同で検出する。
方針：左右の値が等しければ、元の恒等分解の両項が等しい。
規約：全切断位置と任意の安定模型に成立する。
使われ方：障害余核の Segal 比較の単射側。 -/
lemma cutKZero_jointly_injective (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (a b : TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier))
    (hl : cutKZeroRestriction X (cutLeftIntervalInclusion n k) a =
      cutKZeroRestriction X (cutLeftIntervalInclusion n k) b)
    (hr : cutKZeroRestriction X (cutRightIntervalInclusion n k) a =
      cutKZeroRestriction X (cutRightIntervalInclusion n k) b) : a = b := by
  have ha := DFunLike.congr_fun (cutKZero_interval_decomposition n k X) a
  have hb := DFunLike.congr_fun (cutKZero_interval_decomposition n k X) b
  exact ha.trans ((congrArg₂ (· + ·)
    (congrArg (cutKZeroRestriction X (cutLeftIntervalRetraction n k)) hl)
    (congrArg (cutKZeroRestriction X (cutRightIntervalRetraction n k)) hr)).trans hb.symm)

end SerrePositivity.KST.SConstruction.Cofinality
