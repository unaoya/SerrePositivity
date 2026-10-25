module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
/-!
概要：次数を持つ互いに逆な cochain の中間対を、六項合成から消去する。
方針：全次数の成分を同じ中間添字で評価し、実際の分裂恒等式を合成する。
規約：シフトや閉射を仮定せず、全ての次数の等式を明示する。
使われ方：coherent bar の shift ブロック合成の厳密な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K M N T P L : Complex R}

lemma cochainSixfold_cancel {s t r p q a b c : ℤ}
    (A : Cochain K M s) (f : Cochain M N p) (U : Cochain N T (-t))
    (V : Cochain T N t) (g : Cochain N P q) (B : Cochain P L (-r))
    (hUV : U.comp V (neg_add_cancel t) = Cochain.ofHom (𝟙 N))
    (ha : s + p - t = a) (hb : t + q - r = b) (hc : a + b = c) :
    ((A.comp f rfl).comp U (by omega : s + p + -t = a)).comp
        ((V.comp g rfl).comp B (by omega : t + q + -r = b)) hc =
      (A.comp (f.comp g rfl) rfl).comp B (by omega : s + (p + q) + -r = c) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ hc i (i + a) j rfl (by omega)]
  rw [Cochain.comp_v _ _ _ i (i + s + p) (i + a) (by omega) (by omega)]
  rw [Cochain.comp_v _ _ _ (i + a) (i + s + p + q) j (by omega) (by omega)]
  rw [Cochain.comp_v A f rfl i (i + s) (i + s + p) rfl rfl]
  rw [Cochain.comp_v V g rfl (i + a) (i + s + p) (i + s + p + q)
    (by omega) rfl]
  rw [Cochain.comp_v _ B _ i (i + s + p + q) j (by omega) (by omega)]
  rw [Cochain.comp_v A _ rfl i (i + s) (i + s + p + q) rfl (by omega)]
  rw [Cochain.comp_v f g rfl (i + s) (i + s + p) (i + s + p + q) rfl rfl]
  have hm := Cochain.congr_v hUV (i + s + p) (i + s + p) (by omega)
  rw [Cochain.comp_v U V _ (i + s + p) (i + a) (i + s + p)
    (by omega) (by omega), Cochain.ofHom_v, HomologicalComplex.id_f] at hm
  have hcomp := congrArg (fun k : (N.X (i + s + p) ⟶ N.X (i + s + p)) =>
    A.v i (i + s) rfl ≫ f.v (i + s) (i + s + p) rfl ≫ k ≫
      g.v (i + s + p) (i + s + p + q) rfl ≫
      B.v (i + s + p + q) j (by omega)) hm
  simpa only [Category.assoc, Category.id_comp] using hcomp

end SerrePositivity.DifferentialGraded
