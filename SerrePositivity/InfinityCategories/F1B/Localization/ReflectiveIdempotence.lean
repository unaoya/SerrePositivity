module

public import SerrePositivity.InfinityCategories.F1B.Localization.Reflective
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexFunctorFaithful
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.QCatPostcompFaithful
public import SerrePositivity.InfinityCategories.F1B.Adjunction.RepresentableAdjunction

/-!
概要：反射的包含の余単位の可逆性と反射関手の冪等性。
方針：h Fun の後合成の充満忠実性を双圏へ移し、通常の Hom 圏の随伴の定理を使う。
規約：余単位の可逆性や冪等性を追加仮定にしない。
使われ方：Kerodon Cor 6.2.2.26 と反射的局所化の普遍性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
local instance reflectiveHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：h Fun の右後合成が充満忠実な随伴の余単位は h Fun で可逆。
方針：充満忠実性を QCat の Hom 圏へ移して双圏の一般補題を使う。
規約：対象ごとの h の等式で代用しない。使われ方：反射的包含の余単位。 -/
lemma QCatAdjunction.counitHom_isIso_of_postcompFullyFaithful
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (h : (hoFunctor.map ((ihom Y).map G)).toFunctor.FullyFaithful) : IsIso a.counitHom := by
  haveI : IsIso a.counit :=
    bicategory_counit_isIso_of_postcomp_fullyFaithful a (qcatPostcompFullyFaithfulOfHo Y Y X G h)
  change IsIso ((qcatHomFunctor Y Y).map a.counit)
  infer_instance

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : ReflectiveSubcategory X P)

/-- 概要：反射の余単位は QCat の Hom 圏でも可逆。
方針：包含の h Fun の後合成の充満忠実性を双圏へ移す。
規約：h Fun での可逆性と同じ二胞体の主張。
使われ方：三角恒等式による単位の whisker の可逆性。 -/
instance counit_isIso : IsIso r.adjunction.counit :=
  bicategory_counit_isIso_of_postcomp_fullyFaithful r.adjunction
    (qcatPostcompFullyFaithfulOfHo _ _ _ _
      (fullSubcomplexFunctorInclusionHoFullyFaithful _ X P))

/-- 概要：反射の余単位は h Fun 全体で可逆。
方針：包含の任意の関手 ∞ 圏での充満忠実性と随伴の一般補題を使う。
規約：反射の定義には余単位の可逆性を含めない。
使われ方：部分圏での反射の回収と冪等性。 -/
instance counitHom_isIso : IsIso r.adjunction.counitHom :=
  r.adjunction.counitHom_isIso_of_postcompFullyFaithful
    (fullSubcomplexFunctorInclusionHoFullyFaithful _ X P)

/-- 概要：部分圏から反射して戻る合成と恒等関手の自然同型。
方針：証明した余単位の可逆性からその余単位を順射とする同型を取る。
規約：元の随伴の余単位を保持する。使われ方：局所化関手の冪等性。 -/
def counitIso : FunctorIso ((fullSubcomplexOnVertices X P).ι ≫ r.reflector)
    (𝟙 (fullSubcomplexOnVertices X P : SSet.{u})) :=
  asIso r.adjunction.counitHom

/-- 概要：反射自己関手は h Fun で冪等。
方針：部分圏での余単位同型に reflector と包含を前後合成する。
規約：厳密な自己関手の等式には強めない。
使われ方：反射的局所化の冪等性。 -/
def idempotentIso : FunctorIso (r.localization ≫ r.localization) r.localization := by
  simpa only [localization, Category.assoc, Category.id_comp] using
    FunctorIso.postcomp (FunctorIso.precomp r.counitIso r.reflector)
      (fullSubcomplexOnVertices X P).ι

end ReflectiveSubcategory
end SerrePositivity.InfinityCategories
