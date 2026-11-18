module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorTransport

/-!
模型。文献の定義との比較は後で
# 同じ切断の色別の面生成元の置換

Berger–Fresse §2.2.4–6、M14 L11 の証明分割。
位置集合は同じ順序のまま、色の名前だけを替える。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- C334：色を同時に置換すると、元の色別位置集合はそのまま（BF §2.2.4）。 -/
lemma colorPositions_rename {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (σ : Equiv.Perm (Fin r)) (a : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s (σ ∘ v) (σ a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v a := by
  ext i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label, Function.comp_apply]
  exact σ.injective.eq_iff

/-- C335：同じ色の出力次数を、置換後の色で読む（BF §2.2.4）。 -/
lemma outputDegree_rename {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (σ : Equiv.Perm (Fin r)) (a : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v) (σ a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree
  exact congrArg (fun t => t.card - 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_rename s v.val σ a)

variable (A : Type u) [CommRing A]

/-- 元の切断テンソルの一因子を、同じ次数と面生成元の対で読む記法（BF §2.2.6）。 -/
def cutVector {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (x : S _⦋q⦌) :
    Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x)⟩

/-- C336：同じ位置集合・同じ順序で指定した面生成元は、色置換で変わらない（BF §2.2.6）。 -/
lemma cutVector_rename_image {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (a : Fin r) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v) (σ a) x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector A S s v a x := by
  let F : {t : Finset (Fin (m + q + 1)) // t.Nonempty} →
      Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)) := fun t =>
    let e := t.val.orderEmbOfFin (by
      have ht := Finset.card_pos.mpr t.property
      omega : t.val.card = t.val.card - 1 + 1)
    let θ : Fin (t.val.card - 1 + 1) →o Fin (q + 1) :=
      ⟨fun i => s.vertical (e i), s.vertical.monotone.comp e.monotone⟩
    ⟨t.val.card - 1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (t.val.card - 1) (S.map (SimplexCategory.mkHom θ).op x)⟩
  change F ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v).val (σ a),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_nonempty s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v) (σ a)⟩ =
    F ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v.val a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_nonempty s v a⟩
  apply congrArg F
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_rename s v.val σ a

/-- C337：色別の同じ因子の族は、逆置換との前合成で読む（BF §2.2.6）。 -/
lemma cutVector_rename {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (x : S _⦋q⦌) :
    (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v) a x) =
      (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector A S s v a x) ∘ σ.symm := by
  funext a
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector_rename_image A S s v σ (σ.symm a) x
  simpa only [Equiv.apply_symm_apply, Function.comp_apply] using h

/-- C338：同じ因子の対の記法は、元のcutTensorの終域を移したもの（BF §2.2.6）。 -/
lemma cutTensor_vectorTensorAt {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌) (t : ℤ)
    (h : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v) : ℤ) = t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutVector A S s v a x) t h =
      (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s v x) := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
