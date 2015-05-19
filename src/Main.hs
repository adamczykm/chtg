module Main where

import System.Environment
import Control.Monad (guard)

import Data.Graph.Inductive
import qualified Data.Set as S
import Data.Set (fromList, toList)
import qualified Data.IntMap as IM
import Data.List (partition,sortBy,minimumBy, maximumBy)
import Data.Function (on)

import qualified Debug.Trace as T

-- =================== Zdefiniowane typy

-- | Typ naszego grafu
type Graf = Gr (Maybe Color) ()

-- | Graf pokolorowany
type ColoredGraf = Gr (Color) ()

-- | Kolor wierzcholka
type Color = Int

-- | Funkcja wybierajaca kolejnosc
type Order = Graf -> [Node]

-- | Algorytm 
type Algorithm = Graf -> ColoredGraf


-- =================== Kolejności brania wierzchołków

-- | Largest First
lfOrder :: Order
lfOrder g = reverse . sortBy (compare `on` deg g) . reverse $ nodes g

-- | Smallest Last
slOrder :: Order
slOrder g' = reverse $ map snd $ slWorker [] g'
  where slWorker :: [(Int, Node)] -> Graf -> [(Int, Node)]
        slWorker xs g | g == empty = xs
        slWorker xs g              = slWorker ((deg g sm, sm):xs)
                                              (delNode sm g)
          where sm      = minimumBy cmp (nodes g)
                cmp x y = let s = (compare `on` deg g) x y
                          in case s of
                              EQ -> (compareLowerIsGreater `on` id) x y
                              _  -> s
                              

-- | DSatur
dsOrder :: Order
dsOrder g = if ns' == []
            then []
            else reverse $ go initialSatur []

  where go :: IM.IntMap Int -> [Node] -> [Node]
        go ds ord = case viewMaxValue ds of
                     Nothing       -> ord
                     Just (k, nds) -> go (updateDs (safeNeighbors g k) nds)
                                         (k:ord)

          where updateDs xs nds = foldr (IM.update (Just . succ)) nds xs
                viewMaxValue im | im == IM.empty = Nothing
                viewMaxValue im                  = Just (fst m, rest)
                  where m       = maximumBy cmp $ IM.toList im
                        rest    = IM.delete (fst m) im
                        cmp x y = let s = (compare `on` snd) x y
                                  in case s of
                                   EQ -> (compareLowerIsGreater `on` fst) x y
                                   _  -> s

        ns' = lfOrder g
        initialSatur = IM.fromList $ zip ns' (1 : repeat 0)

-- =================== Algorym kolorowania

-- | Funkcja dla danej kolejnosci wybierania wierzcholkow z grafu
--   zwraca poprawnie (zgodnie z warunkami zadania) pokolorwany graf
colorGraphWithOrder :: Order -> Graf -> ColoredGraf
colorGraphWithOrder order g = go (order g) empty
  where go :: [Node] -> ColoredGraf -> ColoredGraf
        go []     cg = cg
        go (n:ns) cg = go ns (withNodeColored cg
                                              n
                                              newcolor)
          where newcolor = pickColor cg n


        -- | Zwraca graf z wierzcholkiem pomalowanym na dany kolor
        withNodeColored :: ColoredGraf -> Node -> Color -> ColoredGraf
        withNodeColored cg n c = case match n g of
          (Just (p, _, _, s), _) -> (f p, n, c,f s) & cg
            where f = filter (\(_,n') -> n' `gelem` cg)
          (Nothing,           _) -> error "not existent node!?"


        -- | Wybiera najmniejszy możliwy dla wierzchołka kolor
        --   zgodny z warunkami zadania.
        pickColor :: ColoredGraf -> Node -> Color
        pickColor cg n = head $ filter (tryColor cg n) [1..maxColor]
          where maxColor = case safeOnEmpty maximum $ toList (colors cg) of
                            Nothing -> 1
                            Just c  -> c + 1

        -- | Zwraca czy pokolorowanie wierzcholka na dany kolor spełnia
        --   warunki zadania.
        tryColor :: ColoredGraf -> Node -> Color -> Bool
        tryColor cg n c = case IM.lookup c colorsCount of
            Just _  -> False
            -- podzial na dwie klasy kolorów:
            -- scn - co najwyzej jeden sasiad n w tym kolorze
            -- mcn - wiecej niz jeden sasiad n w tym kolorze
            Nothing -> let (scn, mcn) =
                            partition ((==Just 1) .
                                       (flip IM.lookup) colorsCount .
                                       color cg)
                                      neighs
                      in not (startsPath scn) && not (inPath mcn)

          where -- | czy stanie się początkiem scieżki o dl. 3
                startsPath scn = some $ do
                  n1 <- scn
                  n2 <- safeNeighbors cg n1
                  guard (n2 /= n && color cg n2 == c)
                  n3 <- safeNeighbors cg n2
                  guard (n3 /= n1 && color cg n3 == color cg n1)

                -- | Czy bedzie czescią scieżki o dl. 3?
                inPath mcn = some $  do
                  n1 <- mcn
                  n2 <- safeNeighbors cg n1
                  guard (n2 /= n && color cg n2 == c)

                -- | Sasiedzi wierzchołka n, w pokolorowanej czesci grafu.
                neighs = filter (\x -> x `gelem` cg) (safeNeighbors g n)

                -- | Pomocniczy slownik ilosci kolorów
                colorsCount = foldr inc IM.empty (map (color cg) neighs)
                  where inc c' ccs = case IM.lookup c' ccs of
                                     Nothing -> IM.insert c' (1 :: Integer) ccs
                                     Just i  -> IM.insert c' (i + 1)        ccs

printAnswer :: ColoredGraf -> String
printAnswer cg = "Ilość kolorów: " ++ show (maximum $ toList (colors cg))
                 ++ "\nKolorowanie: " ++ show (labNodes cg)

-- =================== Funcje pomocnicze

-- graphInducedByVertices :: gr a b -> [Node] -> gr a b
-- graphInducedByVertices g ns = mkGraph ns ledges
--   where ledges = efilter (\(v1,v2) -> v1 `elem` ns &&
--                                       v2 `elem` ns) ns

-- | Zwraca kolor wierzcholka w grafie g
color :: ColoredGraf -> Node -> Color
color g n = case lab g n of
           Just c  -> c
           Nothing -> error $ show g

-- | Zwraca wszystkie kolory w grafie
colors :: ColoredGraf -> S.Set Color
colors cg | cg == empty = S.empty
colors cg               = fromList $ map (color cg) (nodes cg)

-- | Zwraca sasiadow wierzcholka w grafie
safeNeighbors :: (Graph gr, Eq (gr a b)) => gr a b -> Node -> [Node]
safeNeighbors g _ | g == empty = []
safeNeighbors g n              = neighbors g n

-- | Prawda <=> pusta lista
none :: [a] -> Bool
none [] = True
none _  = False

-- | Prawda <=> niepusta lista
some :: [a] -> Bool
some = not . none

-- | Zwraca Nothing zamiast rzucac wyjatki
safeOnEmpty :: ([a] -> b) -> [a] -> Maybe b
safeOnEmpty _ [] = Nothing
safeOnEmpty f xs = Just $ f xs

-- | Usuwa duplikaty z listy
unique :: Ord a => [a] -> [a]
unique = toList . fromList

-- | Konwersja Int -> Bool
fromInt :: Int -> Bool
fromInt 0 = False
fromInt _ = True

graphSize :: Graf -> Int
graphSize = length . nodes

compareLowerIsGreater :: Ord a => a -> a -> Ordering
compareLowerIsGreater x y = rev $ compare x y
  where rev EQ = EQ
        rev GT = LT
        rev LT = GT

dbg :: Show a => String -> a -> a
dbg s a = T.traceStack (s ++ ": " ++ (show a) ++ "\n") a

-- ================== Funkcje testujące

-- | Sprawdza czy graf g posiada sciezke o dlugosci n.
hasPathWithLengthN :: Int -> Graf -> Bool
hasPathWithLengthN n g = any (== n) pathLengths
  where pathLengths = concat $ (map . map) snd dists
        dists       = map (\x -> level x (undir g)) $
                          map head (components g)

checkColoring :: ColoredGraf -> Bool
checkColoring cg = (not $ any hasSameColoredNeighbour (nodes cg))
                   &&
                   (not $ any colorsInducePath everyPairOfColors)
  where hasSameColoredNeighbour n = col n `elem` map col
                                                     (neighbors cg n)

        colorsInducePath = undefined

        everyPairOfColors = let cs = toList $ colors cg
                            in [(c1,c2) | c1 <- cs, c2 <- cs, c1 /= c2]

        
                               
        col = color cg


-- -- | Ten test sprawdza poprawnosc kolorowania grafu ( czy spelnia warunek),
-- --   Nie sprawdza czy znalezione rozwiazanie jest najmniejsze.
-- test :: Algorithm -> Graf -> ColoredGraf
-- test alg g = not $ any id $ map (hasPathWithLengthN 3) inducedGraphs
--   where (_, col) = alg g
--         inducedGraphs = map (_graphInducedByColors g col)
--                             (everyPairOfColors _colors)
--         _colors = unique $ map ( fromJust . col) (nodes g)



-- ================== Funkcje parsujące

-- | Convert list of lists of neighbours to graf
fromNeighbourhoodList :: [[Node]] -> Graf
fromNeighbourhoodList nss = fixGraph $ mkGraph (zip names (repeat Nothing)) ledges
  where names = [1..(length nss)]
        
        ledges = concat $ map (uncurry edgesFromNs) (zip names nss)
        
        edgesFromNs n = map (\x -> (n, x, ()))
        
        fixGraph g' = undirG $ clearSelfEdges $ addMissingNodes g' (nodesFromEdges g')
        
          where nodesFromEdges = unique .
                                 foldl (\xs (v1,v2) -> v1 : v2 : xs) [] .
                                 edges

                clearSelfEdges g = efilter (\(v1,v2, _) -> v1 /= v2) g

                undirG g = foldr delEdge (undir g)
                                 [(v1,v2) |
                                  v1 <- [1..(graphSize g)],
                                  v2 <- [(v1+1)..(graphSize g)]]

                addMissingNodes g []     = g
                addMissingNodes g (n:ns) | notElem n (nodes g)
                                         = addMissingNodes (insNode (n,Nothing) g) ns
                addMissingNodes g (_:ns) = addMissingNodes g ns


parseFromNeighbourMatrix :: String -> Graf
parseFromNeighbourMatrix = fromMatrix . readMatrix
  where readMatrix :: String -> [[Bool]]
        readMatrix = (map . map) (fromInt . read) . map words . lines

        fromMatrix :: [[Bool]] -> Graf
        fromMatrix = fromNeighbourhoodList . map neighbours
          where neighbours = (map fst) .
                             filter ((== True) . snd) .
                             zip [1..]

readFromMatrixFile :: FilePath -> IO Graf
readFromMatrixFile = parseGraphFromFileWith parseFromNeighbourMatrix


parseGraphFromFileWith :: (String -> Graf) -> FilePath -> IO Graf
parseGraphFromFileWith parseFun fp = do
  gstr <- readFile fp
  return $ parseFun gstr

graphFromNeighbourList :: String -> Graf
graphFromNeighbourList = fromNeighbourhoodList . readNeighbourhoodList
         where readNeighbourhoodList :: String -> [[Node]]
               readNeighbourhoodList = (map . map) read  . map words . lines 


-- ======================== Main

main :: IO ()
main = do
  g  <- getArgs   >>= readFromMatrixFile . (!! 0)

  putStrLn $ "== Largest First: " ++ (show $ lfOrder g)
  putStrLn $ printAnswer $ colorGraphWithOrder lfOrder g

  putStrLn $ "== Smallest Last: " ++ (show $ slOrder g)
  putStrLn $ printAnswer $ colorGraphWithOrder slOrder g

  putStrLn $ "== DSatur: " ++ (show $ dsOrder g)
  putStrLn $ printAnswer $ colorGraphWithOrder dsOrder g

  return ()

  
