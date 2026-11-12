module
public import SerrePositivity.KST.SConstruction.SOneExact
public import SerrePositivity.KST.SConstruction.MultiRealization
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 反復 S の一次方向の自然な比較
概要：外側の S の次数を 1 に固定した多単体図式から残りの反復へ自然に写す。
方針：安定圏の S₁ 比較を反復の各入力へ適用し、core と対角実現へ移す。
規約：自然な逆射を選択しない。使われ方：反復間の suspension 構造射の源の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：反復の先頭方向を次数 1 に固定する添字関手。
方針：先頭に定値 [1]、残りに各座標の評価を配置する。
規約：先頭の S は最も外側。使われ方：一次方向の比較の源。 -/
def oneDirectionIndex (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (Fin (r + 1) → SimplexCategoryᵒᵖ) :=
  Functor.pi' (fun i => Fin.cases
    ((Functor.const (Fin r → SimplexCategoryᵒᵖ)).obj (Opposite.op ⦋1⦌))
    (fun j => Pi.eval (fun _ : Fin r => SimplexCategoryᵒᵖ) j) i)

/-- 概要：先頭を一次に固定した反復自己関手から残りの反復への自然変換。
方針：残りの反復の後で S₁ の比較を適用する。
規約：安定圏での射として定義する。使われ方：多単体的比較の自然性。 -/
def multiSOneEndofunctorComparison (r : ℕ) :
    oneDirectionIndex r ⋙ multiSEndofunctor (r + 1) ⟶ multiSEndofunctor r where
  app d := Functor.whiskerLeft ((multiSEndofunctor r).obj d) stableSOneComparisonNat
  naturality {d e} f := by
    apply NatTrans.ext
    funext X
    exact stableSOneComparisonNat.naturality (((multiSEndofunctor r).map f).app X)

/-- 概要：一次に固定した多単体的反復から残りの反復への比較。
方針：自己関手の比較を入力で評価し、底の単体集合へ忘れる。
規約：全方向での厳密な自然変換。使われ方：core の比較の入力。 -/
def multiSOneComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionIndex r ⋙ multiSConstruction (r + 1) X ⟶ multiSConstruction r X :=
  Functor.whiskerRight (multiSOneEndofunctorComparison r)
    ((evaluation StableModel.{u} StableModel.{u}).obj X ⋙ stableModelForget)

/-- 概要：各多次数の一次方向の比較は既存の S₁ の比較。
方針：反復自己関手の評価を計算する。
規約：全単体での厳密な等号。使われ方：各段の充填性の証明。 -/
lemma multiSOneComparison_app (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiSOneComparison r X).app d = sOneComparison ((multiSConstruction r X).obj d) := rfl

/-- 概要：一次方向の比較は各多次数で trivial Kan fibration。
方針：残りの反復の安定性と S₁ の比較の充填性を使う。
規約：追加の補完仮定なし。使われ方：core と実現の弱同値の比較。 -/
instance multiSOneComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((multiSOneComparison r X).app d) := by
  rw [multiSOneComparison_app]
  infer_instance

/-- 概要：一次方向の多単体的比較に core を適用する。
方針：core 関手による後合成。
規約：各段は Kan。使われ方：実現の比較。 -/
def multiCoreSOneComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X ⟶ multiCoreSConstruction r X :=
  Functor.whiskerRight (multiSOneComparison r X) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：core の一次方向の比較も各段で trivial Kan fibration。
方針：元の比較の充填性を core に制限する。
規約：源・標的の quasicategory 性は反復の安定性から得る。使われ方：対角比較。 -/
instance multiCoreSOneComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((multiCoreSOneComparison r X).app d) := by
  have : Quasicategory ((oneDirectionIndex r ⋙ multiSConstruction (r + 1) X).obj d) := by
    change Quasicategory ((multiSConstruction (r + 1) X).obj ((oneDirectionIndex r).obj d))
    infer_instance
  exact coreMap_trivialKanFibration ((multiSOneComparison r X).app d)

/-- 概要：一次方向の比較を残りの方向の対角上の図式に制限する。
方針：対角添字関手による前合成。
規約：実現前の単体的 Kan 複体間の射。使われ方：局所化の対角定理。 -/
def oneDirectionDiagonalComparison (r : ℕ) (X : StableModel.{u}) :
    multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X ⟶
      multiIndexDiagonal r ⋙ multiCoreSConstruction r X :=
  Functor.whiskerLeft (multiIndexDiagonal r) (multiCoreSOneComparison r X)

/-- 概要：先頭を一次に固定した反復の対角実現から残りの反復実現への射。
方針：残りの方向と core の次数の対角を取る。
規約：源の先頭の次数は常に 1。使われ方：構造射の源を比較する弱同値。 -/
def oneDirectionRealizationComparison (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj
      (multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X) ⟶
        multiDiagonalCoreSConstruction r X :=
  simplicialDiagonalFunctor.map (oneDirectionDiagonalComparison r X)

/-- 概要：一次方向を消す比較は対角実現後に局所化で可逆。
方針：各段の trivial Kan fibration と HA の対角定理を使う。
規約：対角実現自体の Kan 性は仮定しない。使われ方：構造射の源の比較。 -/
lemma oneDirectionRealizationComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (oneDirectionRealizationComparison r X)) := by
  apply SerrePositivity.BisimplicialModel.localized_diagonal_map
    (oneDirectionDiagonalComparison r X)
  intro d
  exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
    ((multiCoreSOneComparison r X).app ((multiIndexDiagonal r).obj d))

/-- 概要：一次方向を消す多単体的比較は入力の射と可換。
方針：安定自己関手間の自然変換の自然性を底の射へ移す。
規約：全 cofiber 保存射を含む。使われ方：core と実現の自然性。 -/
lemma multiSOneComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Functor.whiskerLeft (oneDirectionIndex r) ((multiSConstructionFunctor (r + 1)).map f) ≫
        multiSOneComparison r Y =
      multiSOneComparison r X ≫ (multiSConstructionFunctor r).map f := by
  apply NatTrans.ext
  funext d
  exact congrArg Subtype.val (((multiSOneEndofunctorComparison r).app d).naturality f)

/-- 概要：core の一次方向の比較も入力の射と可換。
方針：元の比較の等式に core 関手を適用する。
規約：各方向の自然性を保つ。使われ方：実現の比較の自然変換。 -/
lemma multiCoreSOneComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Functor.whiskerLeft (oneDirectionIndex r) ((multiCoreSConstructionFunctor (r + 1)).map f) ≫
        multiCoreSOneComparison r Y =
      multiCoreSOneComparison r X ≫ (multiCoreSConstructionFunctor r).map f := by
  exact congrArg ((Functor.whiskeringRight _ _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor).map
    (multiSOneComparison_naturality r f)

/-- 概要：一次方向の比較を入力についての自然変換にまとめる。
方針：各入力に多単体的 core の比較を置く。
規約：逆射の選択なし。使われ方：各実現の自然な比較の入力。 -/
def multiCoreSOneComparisonNat (r : ℕ) :
    multiCoreSConstructionFunctor (r + 1) ⋙
      (Functor.whiskeringLeft _ _ _).obj (oneDirectionIndex r) ⟶
        multiCoreSConstructionFunctor r where
  app := multiCoreSOneComparison r
  naturality {_X _Y} f := multiCoreSOneComparison_naturality r f

/-- 概要：先頭を一次に固定した反復の残りの対角実現の関手。
方針：入力の関手から添字の制限と対角を取る。
規約：反復数ゼロも許す。使われ方：構造射の源の比較。 -/
def oneDirectionRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ SSet.{u} :=
  multiCoreSConstructionFunctor (r + 1) ⋙
    (Functor.whiskeringLeft _ _ _).obj (oneDirectionIndex r) ⋙
      (Functor.whiskeringLeft _ _ _).obj (multiIndexDiagonal r) ⋙ simplicialDiagonalFunctor

/-- 概要：一次方向を消す対角実現の比較は入力について自然。
方針：多単体的自然変換を対角と実現で後合成する。
規約：局所化前の厳密な自然変換。使われ方：構造射の比較の関手性。 -/
def oneDirectionRealizationComparisonNat (r : ℕ) :
    oneDirectionRealizationFunctor r ⟶ multiRealizationFunctor r :=
  Functor.whiskerRight (multiCoreSOneComparisonNat r)
    ((Functor.whiskeringLeft _ _ _).obj (multiIndexDiagonal r) ⋙ simplicialDiagonalFunctor)

/-- 概要：実現の自然変換の成分は既存の比較。
方針：前合成と対角の定義を計算する。
規約：厳密な等号。使われ方：局所化可逆性を自然変換の成分に適用する。 -/
lemma oneDirectionRealizationComparisonNat_app (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionRealizationComparisonNat r).app X = oneDirectionRealizationComparison r X := rfl

end SerrePositivity.KST.SConstruction
