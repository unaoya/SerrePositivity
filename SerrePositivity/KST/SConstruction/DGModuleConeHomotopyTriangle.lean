module
public import SerrePositivity.DifferentialGraded.Module.ConeRotation
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated


/-!
概要：指定加群ホモトピーから同じ実 cone 射の三角形写像と同値判定を作る。
方針：元の包含・connecting 射を全 dg 自然な実 cone 射で回収し、K(D) で照合する。
規約：対象別 chain homotopy の存在で代用しない。使われ方：実逆回転の合成比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M N M' N' : ModuleCategory R D} (f : M ⟶ N) (g : M' ⟶ N')
  (a : M ⟶ M') (b : N ⟶ N') (h : ModuleHomotopy R D (f ≫ b) (a ≫ g))

/-- 概要：指定ホモトピーからの元実 cone 射は標準三角形の写像。
方針：元の全加群ホモトピー・実二辺・shift 比較を回収する。
規約：実 cone 射を変更しない。使われ方：回転比較の二同値からの判定。 -/
def dgModuleConeHomotopyTriangleMap :
    moduleHomotopyConeTriangle R D f ⟶ moduleHomotopyConeTriangle R D g where
  hom₁ := (moduleToHomotopy R D).map a
  hom₂ := (moduleToHomotopy R D).map b
  hom₃ := (moduleToHomotopy R D).map (moduleConeMapOfHomotopy R D f g a b h)
  comm₁ := by
    change (moduleToHomotopy R D).map f ≫ (moduleToHomotopy R D).map b =
      (moduleToHomotopy R D).map a ≫ (moduleToHomotopy R D).map g
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact (moduleToHomotopy_map_eq_iff R D _ _).2 ⟨h⟩
  comm₂ := by
    change (moduleToHomotopy R D).map (moduleConeInr R D f) ≫
        (moduleToHomotopy R D).map (moduleConeMapOfHomotopy R D f g a b h) =
      (moduleToHomotopy R D).map b ≫ (moduleToHomotopy R D).map (moduleConeInr R D g)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (moduleToHomotopy R D).map (moduleConeMapOfHomotopy_inr R D f g a b h)
  comm₃ := by
    let Q := moduleToHomotopy R D
    change (Q.map (moduleConeConnecting R D f) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M) ≫
        (Q.map a)⟦(1 : ℤ)⟧' =
      Q.map (moduleConeMapOfHomotopy R D f g a b h) ≫
        (Q.map (moduleConeConnecting R D g) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M')
    rw [← map_comp_shift_comm, moduleConeMapOfHomotopy_connecting, Q.map_comp, Category.assoc]

/-- 概要：元二辺が K(D) 同値なら同じ実 cone 射も K(D) 同値。
方針：元の標準 distinguished 三角形と指定三角形写像を使う。
規約：元射の同値性を回収。使われ方：connecting cone 比較の実同値判定。 -/
lemma dgModuleConeMapOfHomotopy_isIso
    (ha : IsIso ((moduleToHomotopy R D).map a))
    (hb : IsIso ((moduleToHomotopy R D).map b)) :
    IsIso ((moduleToHomotopy R D).map (moduleConeMapOfHomotopy R D f g a b h)) :=
  isIso₃_of_isIso₁₂ (dgModuleConeHomotopyTriangleMap R D f g a b h)
    (moduleHomotopyConeTriangle_distinguished R D f)
    (moduleHomotopyConeTriangle_distinguished R D g) ha hb

end SerrePositivity.KST.SConstruction
