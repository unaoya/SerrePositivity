module

public import SerrePositivity.KST.DerivedGeometry.HomotopyProducts
public import SerrePositivity.KST.DerivedGeometry.KInjectiveLocalizationAdjunction
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：Grothendieck アーベル圏の非有界導来圏に積を構成する。
方針：右直交部分圏は積で閉じ、K-injective 模型との同値で積を移す。
規約：基礎圏の積の完全性を要求しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13.4・36.3.3 の導来逆極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

instance kInjectiveHomotopyObjects_closedIso :
    (kInjectiveHomotopyObjects C).IsClosedUnderIsomorphisms :=
  inferInstanceAs (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.IsClosedUnderIsomorphisms

/--
概要：K-injective ホモトピー対象の性質は積で閉じている。
方針：射を各射影に合成し、右直交性と積の射の一意性を使う。
規約：導来圏の積の存在を前提にしない。
使われ方：TT §3、Toën §3.2、Stacks 19.13.4 の導来積。
-/
instance kInjectiveHomotopyObjects_closedProducts (ι : Type w) :
    (kInjectiveHomotopyObjects C).IsClosedUnderLimitsOfShape (Discrete ι) :=
  .mk' (by
    rintro _ ⟨F, hF⟩ X f hX
    apply limit.hom_ext
    intro a
    simpa using hF a (f ≫ limit.π F a) hX)

/--
概要：K-injective ホモトピー対象の充満部分圏には積がある。
方針：積で閉じた充満部分圏の包含が極限を創出することを使う。
規約：任意の小さい積。
使われ方：TT §3、Toën §3.2 の導来積の模型。
-/
instance kInjectiveHomotopyObjects_hasProducts :
    HasProducts.{w} (kInjectiveHomotopyObjects C).FullSubcategory :=
  fun _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (kInjectiveHomotopyObjects C).ι

/--
概要：元の非有界導来圏に小さい積が存在する。
方針：証明済みの K-injective 模型の同値で積を移送する。
規約：Mathlib の導来圏の定義を維持する。
使われ方：TT §3・§8、Toën §3.2、Stacks 36.3.3 の切断塔の導来逆極限。
-/
instance unboundedDerivedCategory_hasProducts : HasProducts.{w} (DerivedCategory C) :=
  fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (kInjectiveDerivedFunctor C).asEquivalence.inverse

end SerrePositivity.KST.DerivedGeometry
