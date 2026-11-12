module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorCellComparison
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaceEvaluation

/-! # 元の実 dg 関手の全 tensor 生成元像の回収
概要：native HA から読む全生成元値を、元の同端点部分集合生成射の実像と同定する。
方針：生成元語の標準面表示と最高生成元像を、元の次数移送を保って合成する。
規約：実 dg 関手と元の tensor 生成元を保持。使われ方：逆 Hom 射の左逆と微分比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の複体の射は、同じ次数等号による始域・終域の移送と可換。 -/
lemma complexMap_degree_cast {K L : Complex A} (f : K ⟶ L) {p q : ℤ} (h : p = q)
    (x : K.X p) :
    f.f q (eqToHom (congrArg K.X h) x) = eqToHom (congrArg L.X h) (f.f p x) := by
  cases h
  rfl

/-- 元の次数移送後の射の値を逆移送すると、元の同じ次数の値を回収する。 -/
lemma complexMap_degree_cast_cancel {K L : Complex A} (f : K ⟶ L) {p q : ℤ}
    (h : p = q) (x : K.X p) :
    eqToHom (congrArg L.X h.symm) (f.f q (eqToHom (congrArg K.X h) x)) = f.f p x := by
  cases h
  rfl

/-- 実 dg 関手からの全 native HA 生成元値は、元の同じ tensor 生成元の実像。 -/
lemma simplexHAGeneratorValue_map_recovery {D : Type v} [DGCategory A D] {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last m) < b) :
    simplexHAGeneratorValue A (cubicalLambdaNativeSimplexData A F) m i v b hb =
      (simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫
          F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).f
        (serreCubeGeneratorDegree m i) (serreCubeGenerator A m i) := by
  let c := simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫ F.map _ _
  let h := serreCubeGeneratorDegree_freeDimension m i
  have hw := congrArg (fun f =>
    eqToHom (congrArg (fun k => (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X k) h.symm)
      ((f ≫ F.map _ _).f (-(serreCubeGeneratorFreeDimension m i : ℤ))
        (serreCubeTopCell A (serreCubeGeneratorFreeDimension m i))))
    (simplexHAGeneratorWord_cell_standard A m i v b hb)
  have ht := congrArg (fun w => eqToHom (congrArg (fun k => (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X k) h.symm)
    (c.f (-(serreCubeGeneratorFreeDimension m i : ℤ)) w))
      (serreCubeGenerator_face_top A m i)
  exact (simplexHAGeneratorValue_recovery A F m i v b hb).trans
    (hw.trans (ht.trans (complexMap_degree_cast_cancel A c h (serreCubeGenerator A m i))))

end SerrePositivity.KST.SConstruction
