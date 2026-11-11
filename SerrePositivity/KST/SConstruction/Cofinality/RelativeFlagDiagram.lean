module
public import SerrePositivity.KST.SConstruction.Cofinality.WideStageMaps

/-!
概要：同じ S 多次数の相対旗を旗方向の単体的 quasicategory として束ねる。
方針：標準単体間の射の前合成を相対旗へ制限する。
規約：旗間の全高次単体を保ち、まだ実現後の亜群化比較を主張しない。
使われ方：相対 S• 比較の実現前の入力。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ全多次数の相対旗は旗方向で厳密な単体的対象となる。
方針：標準単体の前合成の関手則を部分型の値で検査する。
規約：面・退化ごとに新しく旗の代表を選ばない。
使われ方：相対旗の core と実現を取る前の単体構造。 -/
def multiRelativeFlagDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u})
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := multiRelativeFlags r ι Y M (SSet.stdSimplex.obj n.unop)
  map α := multiRelativeFlagsPrecomp r ι Y M (SSet.stdSimplex.map α.unop)
  map_id n := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    have h : (pre (SSet.stdSimplex.map (𝟙 n.unop))).app
        (((multiSEndofunctor r).obj ι).obj Y).carrier = 𝟙 _ := by
      rw [CategoryTheory.Functor.map_id, pre_id]
      rfl
    exact congrArg (fun q => q.app d s.val) h
  map_comp {n m k} α β := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    have h : (pre (SSet.stdSimplex.map (β.unop ≫ α.unop))).app
        (((multiSEndofunctor r).obj ι).obj Y).carrier =
        (pre (SSet.stdSimplex.map α.unop)).app _ ≫
          (pre (SSet.stdSimplex.map β.unop)).app _ := by
      rw [CategoryTheory.Functor.map_comp, pre_map]
      rfl
    exact congrArg (fun q => q.app d s.val) h

/-- 概要：相対旗の単体的図式の各段で元の全 Kan core を取る。
方針：既存の core 関手との合成で全ての旗間の可逆射を保持する。
規約：wide 内部 Hom の core を代用しない。
使われ方：HLS の相対旗の実現の入力。 -/
def multiRelativeCoreFlagDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u})
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  multiRelativeFlagDiagram r ι Y M ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

end SerrePositivity.KST.SConstruction.Cofinality
