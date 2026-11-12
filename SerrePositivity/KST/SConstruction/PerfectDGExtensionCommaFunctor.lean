module
public import SerrePositivity.KST.SConstruction.DGStrictCommaFunctor
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition

/-! # 元の Perf 延長の合成比較から作る実 comma 関手
概要：二回の実 Perf 延長と一回の合成延長を、元の逆比較付きで comma へ送る。
方針：合成比較の全 Hom 自然性から逆比較の自然性を得て、厳密関手の構成へ適用する。
規約：同型の選び直しをしない。使われ方：標準対角の実 Perf 比較データ。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 元の二つの実 Perf 延長と、同じ合成比較の逆から作る全 Hom 自然な比較族。 -/
def perfectDGExtensionCommaFamily :
    DGStrictCommaFamily A (PerfectDGModule A E) (PerfectDGModule A T)
      (perfectDGExtension A E T G) (PerfectDGModule A D) where
  source := perfectDGExtension A D E F
  replacement := perfectDGExtension A D T (F.comp G)
  augmentation X := (perfectDGExtensionCompositionAt A D E T F G X).inv
  naturality X Y := (dgFunctorClosedComparison_inv_naturality A
    ((perfectDGExtension A D E F).comp (perfectDGExtension A E T G))
    (perfectDGExtension A D T (F.comp G))
    (perfectDGExtensionCompositionAt A D E T F G)
    (perfectDGExtensionCompositionAt_naturality A D E T F G) X Y).symm

/-- 全 Hom の単位・合成を厳密に保ち、元の逆合成比較を持つ実 Perf comma 関手。 -/
def perfectDGExtensionCommaFunctor :
    DGFunctor A (PerfectDGModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject A (PerfectDGModule A E) (PerfectDGModule A T)
        (perfectDGExtension A E T G)) :=
  (perfectDGExtensionCommaFamily A D E T F G).toDGFunctor

/-- 同じ comma 関手の第一射影は、元の第一の実 Perf 延長そのもの。 -/
lemma perfectDGExtensionCommaFunctor_source :
    (perfectDGExtensionCommaFunctor A D E T F G).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource A (PerfectDGModule A E) (PerfectDGModule A T)
        (perfectDGExtension A E T G)) = perfectDGExtension A D E F :=
  (perfectDGExtensionCommaFamily A D E T F G).toDGFunctor_source

/-- 同じ comma 関手の第二射影は、元の合成入力の実 Perf 延長そのもの。 -/
lemma perfectDGExtensionCommaFunctor_replacement :
    (perfectDGExtensionCommaFunctor A D E T F G).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement A (PerfectDGModule A E) (PerfectDGModule A T)
        (perfectDGExtension A E T G)) = perfectDGExtension A D T (F.comp G) :=
  (perfectDGExtensionCommaFamily A D E T F G).toDGFunctor_replacement

/-- 同じ閉比較は、元の実 Perf 延長合成同型の逆射を回収する。 -/
lemma perfectDGExtensionCommaFunctor_augmentation (X : PerfectDGModule A D) :
    ((perfectDGExtensionCommaFunctor A D E T F G).obj X).augmentation =
      (perfectDGExtensionCompositionAt A D E T F G X).inv := rfl

end SerrePositivity.KST.SConstruction
