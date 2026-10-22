module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransport

/-!
概要：相対 class 経路による実模型の射は、逆経路による射を逆とする実代数同型である。
方針：元の二脚と経路の線形公式で両合成を計算し、三成分の一意性を適用する。
規約：ホモロジー検出を使わず実射の両逆を証明する。使われ方：元の class 模型の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  {q : W ⟶ A} {a b : W ⟶ SquareZero.algebra A N} (v : SquareZero.RelativeWitness q N a b)

lemma transport_congr {w : SquareZero.RelativeWitness q N a b} (h : v.hom = w.hom) :
    transport N v = transport N w := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N)
    b (SquareZero.zeroSection A N)
  · change transport N v ≫ relativeLeft N b = transport N w ≫ relativeLeft N b
    rw [transport_left, transport_left]
  · change transport N v ≫ relativeRight N b = transport N w ≫ relativeRight N b
    rw [transport_right, transport_right]
  · change transport N v ≫ relativePath N b = transport N w ≫ relativePath N b
    apply Mon.Hom.ext
    rw [transport_path_linear, transport_path_linear, h]

lemma transport_comp_reverse : transport N v ≫ transport N v.reverse = 𝟙 (relativeModel N a) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N)
    a (SquareZero.zeroSection A N)
  · change (transport N v ≫ transport N v.reverse) ≫ relativeLeft N a = (𝟙 _) ≫ relativeLeft N a
    rw [Category.assoc, transport_left, transport_left, Category.id_comp]
  · change (transport N v ≫ transport N v.reverse) ≫ relativeRight N a = (𝟙 _) ≫ relativeRight N a
    rw [Category.assoc, transport_right, transport_right, Category.id_comp]
  · change (transport N v ≫ transport N v.reverse) ≫ relativePath N a = (𝟙 _) ≫ relativePath N a
    rw [Category.id_comp]
    apply Mon.Hom.ext
    rw [transport_path_linear_precomp N v.reverse (transport N v)]
    simp only [← Category.assoc, transport_left]
    rw [transport_path_linear N v]
    simp only [Mon.comp_hom', SquareZero.RelativeWitness.reverse_hom_linear,
      comp_add, comp_sub, Category.assoc]
    abel

lemma transport_reverse_comp : transport N v.reverse ≫ transport N v = 𝟙 (relativeModel N b) := by
  have hr : v.reverse.reverse.hom = v.hom := by
    apply Mon.Hom.ext
    rw [SquareZero.RelativeWitness.reverse_hom_linear,
      SquareZero.RelativeWitness.reverse_hom_linear]
    abel
  rw [← transport_congr N v.reverse.reverse hr]
  exact transport_comp_reverse N v.reverse

def transportIso : relativeModel N a ≅ relativeModel N b where
  hom := transport N v
  inv := transport N v.reverse
  hom_inv_id := transport_comp_reverse N v
  inv_hom_id := transport_reverse_comp N v

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
