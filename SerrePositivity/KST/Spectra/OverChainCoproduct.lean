module

public import SerrePositivity.KST.Spectra.OverChainCoordinates
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：BK 重みの各単体次数を共変 representable の実際の余積として表す。
方針：射列の座標の第一成分を余積の添字とし、最後の射に各 cofan の成分を適用する。
規約：通常の図式の圏での余極限の普遍性を証明する。
使われ方：Goerss–Jardine VII §4。BK 重みの Reedy cofibrancy の latching 計算。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.OverChainCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (C : Type u) [SmallCategory C] (n : ℕ)

/-- 各射列の最後の対象からの共変 representable。 -/
def representableFamily (σ : ComposableArrows C n) : C ⥤ Type u :=
  coyoneda.obj (Opposite.op (σ.obj (Fin.last n)))

/-- representable の各成分を最後の射の座標へ含める。 -/
def coordinateInjection (σ : ComposableArrows C n) :
    representableFamily C n σ ⟶ coordinateDiagram C n where
  app _j := ↾fun f ↦ ⟨σ, f⟩
  naturality _ _ _ := rfl

/-- 座標図式を頂点とする representable の cofan。 -/
def coordinateCofan : Cofan (representableFamily C n) :=
  Cofan.mk (coordinateDiagram C n) (coordinateInjection C n)

/-- 座標の最後の射を cofan の指定した成分で評価する。 -/
def coordinateDesc (s : Cofan (representableFamily C n)) : coordinateDiagram C n ⟶ s.pt where
  app j := ↾fun x ↦ (s.inj x.1).app j x.2
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro ⟨σ, g⟩
    exact ConcreteCategory.congr_hom ((s.inj σ).naturality f) g

/-- 座標図式は共変 representable の余積そのもの。 -/
def coordinateCofanIsColimit : IsColimit (coordinateCofan C n) :=
  Cofan.IsColimit.mk _ (coordinateDesc C n)
    (fun s σ ↦ by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro f
      rfl)
    (fun s m hm ↦ by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro ⟨σ, f⟩
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm σ) j) f)

end SerrePositivity.KST.Spectra.OverChainCoordinates
