module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeConnecting

/-!
概要：同じ実 cone 作用を回収する族の指定 connecting 自然性を接続する。
方針：元二射・元二作用の回収を既存の全次数 connecting 式へ代入する。
規約：元閉射・元 Hom 作用を保持する。
使われ方：元 gluing cone の全 connecting 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元実 connecting・元 cone 作用の回収を持つ族は全次数で可換。
方針：同じ元四成分を既存の connecting 自然性へ代入する。
規約：元閉射・全作用を変更しない。使われ方：元実 gluing 族の全 Hom 自然性。 -/
lemma dgModuleConeConnecting_family_naturality {M N P Q : ModuleCategory R D}
    (f : M ⟶ N) (g : P ⟶ Q)
    (c : moduleCone R D f ⟶ M⟦(1 : ℤ)⟧)
    (d : moduleCone R D g ⟶ P⟦(1 : ℤ)⟧)
    (hc : c = moduleConeConnecting R D f) (hd : d = moduleConeConnecting R D g)
    (n : ℤ)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).X n)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) Q)).X n)
    (s : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).X n)
    (t : (moduleHom R D (shiftModule 1 (ForgetEnrichment.to (Complex R) M))
      (shiftModule 1 (ForgetEnrichment.to (Complex R) P))).X n)
    (hs : s = dgGluingModuleConeElement R D f g a b 0 (sub_add_cancel n 1))
    (ht : t = (moduleShiftHom R D 1 _ _).f n a) :
    (eHomWhiskerLeft (Complex R) (moduleCone R D f) d).f n s =
      (eHomWhiskerRight (Complex R) c (P⟦(1 : ℤ)⟧)).f n t := by
  rw [hc, hd, hs, ht]
  exact dgGluingModuleConeElement_connecting R D f g a b 0 (sub_add_cancel n 1)
end SerrePositivity.KST.SConstruction
