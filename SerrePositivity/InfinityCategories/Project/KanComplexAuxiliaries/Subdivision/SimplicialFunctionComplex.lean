module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyProduct

/-!
概要：集合で添字付けられた単体集合の関数複体とその Kan 性。
方針：各単体次数で関数の集合を取り、ホーンを各座標で充填する。
規約：単体的写像空間とは区別し、添字集合を離散的に固定する。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の各次数の π_* の計算。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex
end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex
open _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各次数を添字集合からの関数とする単体集合。
方針：顔・退化を各座標で適用する。
規約：添字集合と単体集合は同じ宇宙に置く。
使われ方：Goerss–Jardine I §7。任意個の同一の Kan 複体の積の具体的な表示。 -/
def obj (S : Type u) (X : SSet.{u}) : SSet.{u} where
  obj n := S → X.obj n
  map f := ↾fun x s ↦ X.map f (x s)
  map_id n := by
    ext x s
    exact congr($(X.map_id n) (x s))
  map_comp f g := by
    ext x s
    exact congr($(X.map_comp f g) (x s))

/-- 概要：関数複体の指定した座標への評価。
方針：各単体次数で関数を評価する。
規約：通常の単体集合の射。
使われ方：Goerss–Jardine I §7。積のホモトピー群への各射影。 -/
def eval (S : Type u) (X : SSet.{u}) (s : S) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X ⟶ X where
  app _ := ↾fun x ↦ x s

/-- 概要：座標ごとの射の族を関数複体への射に束ねる。
方針：各単体次数で座標ごとの値を取る。
規約：任意の始域単体集合を許す。
使われ方：Goerss–Jardine I §7。関係充填とホーン充填の座標ごとの貼り合わせ。 -/
def lift {S : Type u} {X A : SSet.{u}} (f : S → (A ⟶ X)) : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X where
  app n := ↾fun a s ↦ (f s).app n a
  naturality n m g := by
    apply ConcreteCategory.hom_ext
    intro a
    change (fun s ↦ (f s).app m (A.map g a)) = fun s ↦ X.map g ((f s).app n a)
    funext s
    exact congr($((f s).naturality g) a)

@[reassoc (attr := simp)]
lemma lift_eval {S : Type u} {X A : SSet.{u}} (f : S → (A ⟶ X)) (s : S) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s = f s := rfl

lemma hom_ext {S : Type u} {X A : SSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X}
    (h : ∀ s, f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s = g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) : f = g := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro a
  funext s
  exact congr($(NatTrans.congr_app (h s) n) a)

/-- 概要：Kan 複体の関数複体は Kan。
方針：各座標でホーンの充填を選び、全ての充填を一つの射へ束ねる。
規約：添字集合の有限性は不要。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の関数空間の Kan 模型。 -/
instance kanComplex (S : Type u) (X : SSet.{u}) [KanComplex X] : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) := by
  rw [KanComplex.iff]
  intro n i fs hf
  choose a ha using fun s ↦ KanComplex.hornFilling (hf.desc ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s)
  have h : (horn (n + 1) i).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift a = hf.desc := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval]
    exact (ha s).symm
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift a, fun j hj ↦ ?_⟩
  rw [← horn.ι_ι_assoc i j hj, h]
  exact hf.ι_desc j hj

end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
