module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKComposition

/-!
# 元の正規化 BK 錐代表と全 Hom パラメータの行

概要：恒等射から作った元の錐代表に任意次数のHomを前合成する。
方針：同じ零cocycleの射への変換と既存の行の合成則を使う。
規約：IS-W2 B02の指定錐との成分照合の分割。錐代表を選び直さない。
使われ方：HA 1.2.4、実豊穣合成と元のHom–Tot比較の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable {A : Type u} [CommRing A]

/-- 概要：元の行の合成則を指定した終次数rで述べる。
方針：次数の等式による同じ型の移送。
規約：新しい合成ではない。使われ方：HA 1.2.4 の恒等射への特殊化。 -/
theorem homToNormalizedBousfieldKan_rows_comp_of_degree {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) r
      ((homToNormalizedBousfieldKan P X).f r (f.comp g h)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (r - n) (by omega) f) := by
  subst r
  exact homToNormalizedBousfieldKan_rows_comp X p q n f g

/-- 概要：指定錐代表のcochainは元の比較に移した同じ閉元。
方針：既存cocycleのhomOf/ofHomの相互逆。
規約：元の射fからの代表。使われ方：HA 1.2.4 の恒等射からの錐の照合。 -/
theorem normalizedBousfieldKanRepresentative_cochain (P : Complex A)
    (X : CosimplicialObject (Complex A)) (f : P ⟶ (productTotalFunctor A).obj X) :
    Cochain.ofHom (normalizedBousfieldKanRepresentative P X f) =
      (homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f) := by
  simp only [normalizedBousfieldKanRepresentative, Cocycle.cochain_ofHom_homOf_eq_coe]
  rfl

/-- 概要：元の比較の任意次数の行は、元の錐代表への同じ前合成。
方針：行の合成則の後の射を恒等射に取り、同じcocycle代表に戻す。
規約：Koszul符号と元のcochain行を保持。使われ方：HA 1.2.4 のAW成分との接続。 -/
theorem homToNormalizedBousfieldKan_rows_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
        0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n ≫
      homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f) := by
  have hc := homToNormalizedBousfieldKan_rows_comp_of_degree X p 0 p (add_zero p) n f
    (Cochain.ofHom (𝟙 _))
  rw [Cochain.comp_id] at hc
  have hr := normalizedBousfieldKanRepresentative_cochain
    ((productTotalFunctor A).obj X) X (𝟙 _)
  change Cochain.ofHom (normalizedBousfieldKanConeRepresentative X) = _ at hr
  rw [← hr] at hc
  exact hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
