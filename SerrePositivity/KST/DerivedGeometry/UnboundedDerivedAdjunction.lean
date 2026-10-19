module

public import SerrePositivity.KST.DerivedGeometry.UnboundedRightDerivedHomotopy
public import SerrePositivity.KST.DerivedGeometry.HomotopyAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
概要：完全な左随伴と加法的右随伴から非有界導来随伴を構成する。
方針：ホモトピー圏上の随伴、完全左導来の比較同型、構成した非有界右導来の普遍性を使う。
規約：右随伴の完全性や H の平坦性を要求しない。
使われ方：TT §3・§8、Toën §3.2、BvdB Thm 3.1.1 のアフィン係数 Dqc 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v₁ v₂ u₁ u₂
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{w} D] [Abelian D] [IsGrothendieckAbelian.{w} D]
  [HasDerivedCategory C] [HasDerivedCategory.{v₂} D]

/--
概要：加法的右随伴の非有界右導来関手。
方針：ホモトピー関手の後に標準局所化を合成し、K-injective 模型で右導来化する。
規約：全複体の非有界導来圏上で定義する。
使われ方：TT §3、Toën §3.2 の非有界右導来大域切断。
-/
def unboundedRightDerivedFunctor (G : D ⥤ C) [G.Additive] : DerivedCategory D ⥤ DerivedCategory C :=
  unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/--
概要：完全左随伴と加法的右随伴の非有界導来随伴。
方針：左導来の比較同型と右導来の後合成の普遍性を使って、随伴を導来化する。
規約：導来随伴の存在を構造体の未証明フィールドにしない。
使われ方：TT §3・§8、Toën §3.2、BvdB Thm 3.1.1 の実際のアフィン比較。
-/
def unboundedDerivedAdjunction {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ unboundedRightDerivedFunctor G := by
  change F.mapDerivedCategory ⊣ unboundedRightDerivedHomotopy D
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  let W₁ := HomotopyCategory.quasiIso C (.up ℤ)
  let W₂ := HomotopyCategory.quasiIso D (.up ℤ)
  let α := F.mapDerivedCategoryFactorsh.hom
  let β := unboundedRightDerivedHomotopyUnit D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  have := CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W₁ F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh
  letI : (F.mapDerivedCategory ⋙ unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).IsLeftDerivedFunctor
      ((CategoryTheory.Functor.associator _ _ _).inv ≫
        CategoryTheory.Functor.whiskerRight α (unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh))) W₁ :=
    CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W₁
    (F.mapDerivedCategory ⋙ unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh))
    (asIso ((CategoryTheory.Functor.associator _ _ _).inv ≫
      CategoryTheory.Functor.whiskerRight α (unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh))))
  letI : (unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).IsRightDerivedFunctor β W₂ :=
    unboundedRightDerivedHomotopy_isRightDerivedFunctor D
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  letI : (unboundedRightDerivedHomotopy D (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (CategoryTheory.Functor.whiskerRight β F.mapDerivedCategory ≫
        (CategoryTheory.Functor.associator _ _ _).hom) W₂ :=
    unboundedRightDerivedHomotopy_postcomp D
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) F.mapDerivedCategory
  exact (adjunctionHomotopy adj).derived W₁ W₂ α β

end SerrePositivity.KST.DerivedGeometry
