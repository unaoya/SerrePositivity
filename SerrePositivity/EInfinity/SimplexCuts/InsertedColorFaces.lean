module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerOrder
public import SerrePositivity.EInfinity.SimplexCuts.FaceDataCompositionTransport

/-!
# 元の挿入色の指定面は二段の指定面と一致する

Berger–Fresse §2.2.6、M14 L12a のC451の挿入色の成分。
元の全頂点の順序同値により、同じ出力次数と指定面をSigmaの中で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の挿入色の全頂点と、同じ内側Cutの全同色頂点の順序同値（BF §2.2.6）。 -/
def insertedColorPathOrderIso {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)) ≃o
      ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b) :=
  StrictMono.orderIsoOfSurjective (insertedColorPathMap u v k c b)
    (insertedColorPathMap_strictMono u v k c b) (insertedColorPathMap_surjective u v k c b)

/-- 同じ全頂点の順序同値は、元の二段の指定高さを保つ（BF §2.2.6）。 -/
lemma insertedColorPathOrderIso_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical (insertedColorPathOrderIso u v k c b x).val) =
        c.2.vertical x.val :=
  insertedColorPathMap_vertices u v k c b x

/-- 元の挿入色の指定面は同じ二段の面の合成と厳密に一致（BF §2.2.6）。 -/
lemma positiveComposite_inserted_face {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    (⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1)
        (BarrattEccles.insertedPosition m (n + 1) k b),
      vertices c.2 (positiveCompositeCutWord u v k c.1)
        (BarrattEccles.insertedPosition m (n + 1) k b)⟩ :
        Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) =
      ⟨outputDegree (positiveCompositeInnerCut u v k c) (positiveWord v) b,
        (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k).comp
          (vertices (positiveCompositeInnerCut u v k c) (positiveWord v) b)⟩ :=
  faceData_comp_eq_of_colorOrderIso _ _ _ _ _ _ _ (insertedColorPathOrderIso u v k c b)
    (fun x => (insertedColorPathOrderIso_vertices u v k c b x).symm)

end SerrePositivity.EInfinity.SimplexCuts
