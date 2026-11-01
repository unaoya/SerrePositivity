module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition

/-! # 元の実 Perf 合成比較による Hom 共役
概要：二回の実延長の Hom 作用を、元の合成比較による共役で一回の作用へ戻す。
方針：全 Hom 自然性に閉零同型の逆を合成して比較を消す。
規約：実 Perf の全次数 Hom を使う。使われ方：ラベル付き作用の厳密な合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 元の二回延長の Hom 作用は、元の合成同型による共役後に合成入力の作用と等しい。 -/
lemma perfectDGExtensionCompositionAt_conjugation (M N : PerfectDGModule A D) :
    (perfectDGExtension A D E F).map M N ≫
        (perfectDGExtension A E T G).map
          ((perfectDGExtension A D E F).obj M) ((perfectDGExtension A D E F).obj N) ≫
        enrichedClosedIsoConjugation (Complex A)
          (perfectDGExtensionCompositionAt A D E T F G M)
          (perfectDGExtensionCompositionAt A D E T F G N) =
      (perfectDGExtension A D T (F.comp G)).map M N := by
  rw [← Category.assoc]
  exact enrichedConjugation_of_naturality (Complex A)
    (perfectDGExtensionCompositionAt A D E T F G M)
    (perfectDGExtensionCompositionAt A D E T F G N)
    (((perfectDGExtension A D E F).comp (perfectDGExtension A E T G)).map M N)
    ((perfectDGExtension A D T (F.comp G)).map M N)
    (perfectDGExtensionCompositionAt_naturality A D E T F G M N)

end SerrePositivity.KST.SConstruction
