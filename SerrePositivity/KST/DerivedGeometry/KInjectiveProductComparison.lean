module

public import SerrePositivity.KST.DerivedGeometry.DerivedProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：K-injective 複体の積はそのまま導来積を表す。
方針：ホモトピー圏の積を右直交部分圏に持ち上げ、同値関手で導来圏に送る。
規約：層の積の完全性を要求しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13.4・36.3.3 の導来逆極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C] {ι : Type w} (P : ι → CochainComplex C ℤ)
  [∀ a, (P a).IsKInjective]

/--
概要：K-injective な因子の積の右直交部分圏での錐。
方針：複体の積とその射影を充満部分圏に持ち上げる。
規約：各因子の K-injective 性から積の K-injective 性を証明済み。
使われ方：TT §3、Toën §3.2 の導来積の比較。
-/
def kInjectiveProductFan : Fan (fun a =>
    (⟨(HomotopyCategory.quotient C (.up ℤ)).obj (P a),
      CochainComplex.IsKInjective.rightOrthogonal (P a)⟩ :
      (kInjectiveHomotopyObjects C).FullSubcategory)) :=
  Fan.mk ⟨(homotopyProductFan P).pt,
      CochainComplex.IsKInjective.rightOrthogonal (complexProduct P)⟩
    (fun a => ObjectProperty.homMk ((homotopyProductFan P).π.app ⟨a⟩))

/--
概要：右直交部分圏の錐は積である。
方針：完全忠実な包含が極限を反映することを使う。
規約：元のホモトピー圏の積と同じ射影。
使われ方：TT §3、Stacks 19.13.4 の導来積。
-/
def kInjectiveProductIsLimit : IsLimit (kInjectiveProductFan P) :=
  isLimitOfIsLimitFanMkObj (kInjectiveHomotopyObjects C).ι _ _
    (homotopyProductIsLimit P)

/--
概要：K-injective 複体の積の導来対象は導来積である。
方針：証明済みの模型の同値が積を保存することを使う。
規約：実際の Mathlib の局所化 Qh による錐。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13.4 の非有界積の計算。
-/
def derivedKInjectiveProductIsLimit :
    IsLimit ((kInjectiveDerivedFunctor C).mapCone (kInjectiveProductFan P)) :=
  isLimitOfPreserves (kInjectiveDerivedFunctor C) (kInjectiveProductIsLimit P)

end SerrePositivity.KST.DerivedGeometry
