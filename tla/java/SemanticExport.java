// Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Base64;
import java.util.Hashtable;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.semantic.FormalParamNode;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.xml.SymbolContext;
import util.SimpleFilenameToStream;
import util.ToolIO;

/** Export the official semantic graph with lossless string payloads. */
public final class SemanticExport {
    public static void main(String[] args) throws Exception {
        var output = System.out;
        System.setOut(System.err);
        ToolIO.out = System.err;
        ToolIO.err = System.err;
        SpecObj spec = new SpecObj(args[0],
            new SimpleFilenameToStream(Arrays.copyOfRange(args, 1, args.length)));
        int status = SANY.frontEndMain(spec, args[0], System.err);
        if (status != 0 || spec.getErrorLevel() != 0
                || spec.getInitErrors().isFailure() || spec.getParseErrors().isFailure()
                || spec.getSemanticErrors().isFailure() || spec.getRootModule() == null) {
            System.exit(1);
        }
        Document document = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
        Element modules = document.createElement("modules");
        document.appendChild(modules);
        SymbolContext context = new SymbolContext();
        for (ModuleNode module : spec.getExternalModuleTable().getModuleNodes()) {
            modules.appendChild(module.export(document, context));
        }
        // The stock exporter omits theorem/assumption parameters, including
        // parameters introduced by named module instances. Retain SANY's own
        // bindings rather than reconstructing them from source text.
        Hashtable<Integer, ExploreNode> nodes = new Hashtable<>();
        for (ModuleNode module : spec.getExternalModuleTable().getModuleNodes()) {
            module.walkGraph(nodes, ExplorerVisitor.NoopVisitor);
        }
        for (ExploreNode node : nodes.values()) {
            if (node instanceof ThmOrAssumpDefNode) {
                for (FormalParamNode parameter : ((ThmOrAssumpDefNode) node).getParams()) {
                    context.put(parameter, document);
                }
            }
        }
        Element exportedContext = context.getContextElement(document);
        NodeList entries = exportedContext.getElementsByTagName("entry");
        for (int i = 0; i < entries.getLength(); i++) {
            Element entry = (Element) entries.item(i);
            int uid = Integer.parseInt(entry.getElementsByTagName("UID").item(0).getTextContent());
            ExploreNode node = nodes.get(uid);
            if (!(node instanceof ThmOrAssumpDefNode)) continue;
            ThmOrAssumpDefNode theorem = (ThmOrAssumpDefNode) node;
            String tag = theorem.isTheorem() ? "TheoremDefNode" : "AssumeDef";
            NodeList definitions = entry.getElementsByTagName(tag);
            if (definitions.getLength() == 0) continue;
            Element definition = (Element) definitions.item(0);
            Element arity = document.createElement("arity");
            arity.setTextContent(Integer.toString(theorem.getArity()));
            definition.appendChild(arity);
            Element parameters = document.createElement("params");
            for (FormalParamNode parameter : theorem.getParams()) {
                Element item = document.createElement("leibnizparam");
                item.appendChild(parameter.export(document, context));
                parameters.appendChild(item);
            }
            definition.appendChild(parameters);
        }
        modules.insertBefore(exportedContext, modules.getFirstChild());
        Element root = document.createElement("RootModule");
        root.setTextContent(spec.getName());
        modules.insertBefore(root, modules.getFirstChild());
        // XML 1.0 cannot represent every legal TLA+ string character.
        NodeList strings = document.getElementsByTagName("StringValue");
        for (int i = 0; i < strings.getLength(); i++) {
            Element string = (Element) strings.item(i);
            string.setTextContent(Base64.getEncoder().encodeToString(
                string.getTextContent().getBytes(StandardCharsets.UTF_8)));
            string.setAttribute("encoding", "base64-utf8");
        }
        TransformerFactory.newInstance().newTransformer().transform(
            new DOMSource(document), new StreamResult(output));
    }
}
