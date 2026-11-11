module
public import SerrePositivity.KST.SConstruction.StableModels
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Data.List.OfFn

/-! # 反復 S 構成の全多単体構造
概要：任意の有限反復 S• を、全方向で関手的な多単体的対象として構成する。
方針：単体的自己関手の反復を、自己関手の合成の二変数関手で束ねる。
規約：方向の順序はリスト版の有限反復と同じ。使われ方：反復実現と delooping。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：任意の有限反復 S の多単体的自己関手。
方針：先頭の S 自己関手と残りの反復を合成の二変数関手で合成する。
規約：先頭の次数は最も外側の S。使われ方：全方向の面・退化の厳密な作用。 -/
def multiSEndofunctor : (r : ℕ) →
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (StableModel.{u} ⥤ StableModel.{u})
  | 0 => (Functor.const _).obj (𝟭 StableModel.{u})
  | r + 1 =>
      (((Pi.eval (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) 0) ⋙ simplicialStableEndofunctor).prod'
        ((Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) Fin.succ) ⋙ multiSEndofunctor r)) ⋙
          Functor.uncurry.obj (Functor.whiskeringRight StableModel.{u} StableModel.{u} StableModel.{u})

/-- 概要：安定な入力の r 重 S 構成を多単体的単体集合として評価する。
方針：多単体的自己関手を入力で評価し、底の単体集合へ忘れる。
規約：r = 0 は元の入力。使われ方：core と対角実現。 -/
def multiSConstruction (r : ℕ) (X : StableModel.{u}) : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u} :=
  multiSEndofunctor r ⋙ (evaluation StableModel.{u} StableModel.{u}).obj X ⋙ stableModelForget

/-- 概要：反復 S の各多次数の対象は quasicategory。
方針：安定な入力の圏で構成した対象の instance を使う。
規約：多次数は任意。使われ方：各段の Kan core。 -/
instance multiSConstruction_quasicategory (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : Quasicategory ((multiSConstruction r X).obj d) := by
  change Quasicategory ((((multiSEndofunctor r).obj d).obj X).carrier)
  infer_instance

/-- 概要：反復 S の各多次数の対象は安定。
方針：自己関手の値の安定性を使う。
規約：余極限存在の追加仮定なし。使われ方：さらに S を反復する。 -/
instance multiSConstruction_isStable (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((multiSConstruction r X).obj d) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((((multiSEndofunctor r).obj d).obj X).carrier)
  infer_instance

/-- 概要：反復の先頭の次数は最も外側の S_n。
方針：合成関手を対象で評価する。
規約：厳密な等号。使われ方：リスト版との比較。 -/
lemma multiSConstruction_obj_succ (r : ℕ) (X : StableModel.{u})
    (d : Fin (r + 1) → SimplexCategoryᵒᵖ) :
    (multiSConstruction (r + 1) X).obj d =
      sConstruction (d 0).unop.len ((multiSConstruction r X).obj (fun i => d i.succ)) := rfl

/-- 概要：多単体構造の各対象は既存のリスト版の有限反復と一致する。
方針：方向数について帰納する。
規約：方向の順序を変更しない。使われ方：零方向の可縮性の再利用。 -/
lemma multiSConstruction_obj_eq_iterated (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiSConstruction r X).obj d =
      iteratedSConstruction (List.ofFn (fun i => (d i).unop.len)) X.carrier := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [multiSConstruction_obj_succ, List.ofFn_succ]
    change sConstruction _ _ = sConstruction _ _
    rw [ih]

/-- 概要：反復 S の全多次数で Kan core を取る。
方針：core 関手との合成。
規約：全方向の面・退化は関手法則を保つ。使われ方：多単体的 Kan 複体。 -/
def multiCoreSConstruction (r : ℕ) (X : StableModel.{u}) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u} :=
  multiSConstruction r X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：多単体的 core の各段は Kan 複体。
方針：反復 S の quasicategory 性と core の Kan 性を使う。
規約：対角を Kan と主張しない。使われ方：反復実現前の対象。 -/
instance multiCoreSConstruction_kanComplex (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) : KanComplex ((multiCoreSConstruction r X).obj d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex _

/-- 概要：零次数の方向を持つ反復 S は可縮な Kan 複体。
方針：対象をリスト版に同定し、既存の零方向の可縮性を使う。
規約：任意の一方向でよい。使われ方：境界の coherent な潰しの準備。 -/
lemma multiSConstruction_isContractibleKan_of_zero_coordinate (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) (i : Fin r) (hi : (d i).unop.len = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((multiSConstruction r X).obj d) := by
  rw [multiSConstruction_obj_eq_iterated]
  exact iteratedSConstruction_isContractibleKan_of_zero_mem _ X.carrier
    (List.mem_ofFn.mpr ⟨i, hi⟩)

/-- 概要：零次数の方向を持つ反復 core S は可縮な Kan 複体。
方針：リスト版 core の零方向の可縮性に戻す。
規約：全方向の構造射はそのまま保持する。使われ方：境界の処理。 -/
lemma multiCoreSConstruction_isContractibleKan_of_zero_coordinate (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) (i : Fin r) (hi : (d i).unop.len = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((multiCoreSConstruction r X).obj d) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((multiSConstruction r X).obj d) : SSet.{u})
  rw [multiSConstruction_obj_eq_iterated]
  exact iteratedCoreSConstruction_isContractibleKan_of_zero_mem _ X.carrier
    (List.mem_ofFn.mpr ⟨i, hi⟩)

end SerrePositivity.KST.SConstruction
