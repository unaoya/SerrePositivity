module
public import SerrePositivity.KST.SConstruction.DGClosedLeftShiftNaturality

/-!
概要：元閉比較の始域 shift の全自然性を実加群 Hom end で保持する。
方針：元次数零の自然性と同じ shift の各評価を照合する。
規約：次数一の符号を保持。使われ方：実回転比較の元第一成分。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：次数零加群比較の全自然性は始域 shift 後の次数一自然性を与える。
方針：元 cochain の計算を各評価に適用する。
規約：元二成分と全整数次数を保持。使われ方：回転比較の第一成分。 -/
lemma dgModuleClosedLeftShift_naturality {M N M' N' : RightModule R D} {n : ℤ}
    (a : (moduleHom R D M M').X n) (b : (moduleHom R D N N').X n)
    (z : (moduleHom R D M N).X 0) (z' : (moduleHom R D M' N').X 0)
    (h : compose R (x := M) (y := N) (z := N') b z (zero_add n) =
      compose R (x := M) (y := M') (z := N') z' a (add_zero n)) :
    compose R (x := shiftModule 1 M) (y := N) (z := N') b
      (moduleHomLeftShiftElement R D 1 (zero_add 1) z) (add_comm 1 n) =
      n.negOnePow • compose R (x := shiftModule 1 M) (y := shiftModule 1 M') (z := N')
        (moduleHomLeftShiftElement R D 1 (zero_add 1) z')
        ((moduleShiftHom R D 1 M M').f n a) rfl := by
  apply moduleHomElement_ext R D
  intro e
  have he := congrArg ((moduleHomπ R D M N' e).f n) h
  rw [moduleHomCompose_π, moduleHomCompose_π] at he
  rw [moduleHomCompose_π, moduleHomLeftShiftElement_π, Units.smul_def, map_zsmul,
    moduleHomCompose_π, moduleHomLeftShiftElement_π, moduleShiftHomElement_π]
  exact (dgClosedLeftShift_naturality _ _ _ _ he).trans
    (congrArg (fun t => (n.negOnePow : ℤˣ) • t.comp
      (((moduleHomπ R D M' N' e).f 0 z').leftShift 1 1 (zero_add 1)) rfl)
      (shiftHom_apply 1 (M.obj (Opposite.op e)) (M'.obj (Opposite.op e)) n
        ((moduleHomπ R D M M' e).f n a)))

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元全厳密比較の同じ成分を始域 shift した族は次数一で全自然。
方針：元厳密自然性へ同じ加群 Hom shift の計算を適用する。
規約：元比較 cycle を保持。使われ方：同じ回転比較の元第一成分。 -/
lemma dgModuleStrictComparisonLeftShift_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (F.comp (moduleShiftDG R D 1)).obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z)
      (moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app x).val) (add_comm 1 n) =
    n.negOnePow • compose R (x := (F.comp (moduleShiftDG R D 1)).obj x)
      (y := (F.comp (moduleShiftDG R D 1)).obj y) (z := G.obj y)
      (moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app y).val)
      (((F.comp (moduleShiftDG R D 1)).map x y).f n z) rfl :=
  dgModuleClosedLeftShift_naturality R D ((F.map x y).f n z) ((G.map x y).f n z)
    (η.app x).val (η.app y).val (η.naturality z).symm
end SerrePositivity.KST.SConstruction
