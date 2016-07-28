package cbcpsold;

import edu.cmu.cs.ls.keymaerax.core.DifferentialProgram;
import edu.cmu.cs.ls.keymaerax.core.ODESystem;
import edu.cmu.cs.ls.keymaerax.parser.StringConverter;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Document;
import java.awt.*;
import java.util.Map;

/**
 * Created by Andreas on 10.11.2015.
 */
public class ComponentPanel extends JPanel implements DocumentListener {
    public static final int TA_COLUMNS = 20;
    public static final double TEXT_WEIGHT = 1.0;
    public static final double LABEL_WEIGHT = 0.0;
    public static final int TA_ROWS_SMALL = 4;
    public static final int TA_ROWS_LARGE = 10;
    public static final Insets DEFAULT_INSETS = new Insets(2, 2, 2, 2);
    public static final int LABEL_WIDTH = 120;
    private Component c;
    private JTextField tfName;
    private JTextArea taCtrl;
    private JTextArea taPlant;
    private JTextArea taPre;
    private JTextArea taPost;

    private JTextField tfAddVarName;
    private JTextArea tfAddVarProp;

    private JList<String> lVlocal;
    private JList<String> lVglobal;
    private JList<Map<String, String>> lVout;
    private JList<Map<String, String>> lVin;

    private JTextArea taStatus;
    private static final String STATUS_VALID = "Valid";

    public ComponentPanel() {
        super();
        this.setLayout(new BoxLayout(this, BoxLayout.PAGE_AXIS));

        GridBagConstraints gbc = new GridBagConstraints();
        gbc.insets = DEFAULT_INSETS;
        gbc.anchor = GridBagConstraints.NORTHEAST;
        gbc.fill = GridBagConstraints.HORIZONTAL;

        //>> Name
        JPanel namePanel = new JPanel(new GridBagLayout());
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = LABEL_WEIGHT;
        namePanel.add(new JLabel("Name:"), gbc);
        gbc.gridx = 1;
        gbc.weightx = TEXT_WEIGHT;
        tfName = new JTextField(TA_COLUMNS);
        tfName.getDocument().addDocumentListener(this);
        namePanel.add(tfName, gbc);

        this.add(namePanel);

        //>> Program
        JPanel programPanel = new JPanel(new GridBagLayout());
        // ctrl
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = LABEL_WEIGHT;
        programPanel.add(new JLabel("Control:"), gbc);
        gbc.gridx = 1;
        gbc.weightx = TEXT_WEIGHT;
        taCtrl = new JTextArea(TA_ROWS_LARGE, TA_COLUMNS);
        taCtrl.getDocument().addDocumentListener(this);
        programPanel.setAlignmentX(java.awt.Component.CENTER_ALIGNMENT);
        programPanel.setBorder(BorderFactory.createTitledBorder("Program"));
        programPanel.add(new JScrollPane(taCtrl), gbc);

        //plant
        gbc.gridx = 0;
        gbc.gridy += 1;
        gbc.weightx = LABEL_WEIGHT;
        programPanel.add(new JLabel("Plant:"), gbc);
        gbc.gridx = 1;
        gbc.weightx = TEXT_WEIGHT;
        taPlant = new JTextArea(TA_ROWS_SMALL, TA_COLUMNS);
        taPlant.getDocument().addDocumentListener(this);
        programPanel.add(new JScrollPane(taPlant), gbc);

        this.add(programPanel);

        //>> Conditions
        JPanel conditionPanel = new JPanel(new GridBagLayout());
        //pre
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = LABEL_WEIGHT;
        conditionPanel.add(new JLabel("Pre:"), gbc);
        gbc.gridx = 1;
        gbc.weightx = TEXT_WEIGHT;
        taPre = new JTextArea(TA_ROWS_SMALL, TA_COLUMNS);
        taPre.getDocument().addDocumentListener(this);
        conditionPanel.add(new JScrollPane(taPre), gbc);

        //post
        gbc.gridx = 0;
        gbc.gridy += 1;
        gbc.weightx = LABEL_WEIGHT;
        conditionPanel.add(new JLabel("Post:"), gbc);
        gbc.gridx = 1;
        gbc.weightx = TEXT_WEIGHT;
        taPost = new JTextArea(TA_ROWS_SMALL, TA_COLUMNS);
        taPost.getDocument().addDocumentListener(this);
        conditionPanel.add(new JScrollPane(taPost), gbc);

        conditionPanel.setAlignmentX(java.awt.Component.CENTER_ALIGNMENT);
        conditionPanel.setBorder(BorderFactory.createTitledBorder("Conditions"));
        this.add(conditionPanel);

        //>> Variables


        //>> Status
        this.add(new JSeparator());

        JPanel statusPanel = new JPanel(new BorderLayout());
        statusPanel.setBorder(BorderFactory.createTitledBorder("Status"));
        taStatus = new JTextArea(7, TA_COLUMNS);
        taStatus.setEditable(false);
        statusPanel.add(new JScrollPane(taStatus), BorderLayout.CENTER);

        statusPanel.setAlignmentX(java.awt.Component.CENTER_ALIGNMENT);
        this.add(statusPanel, gbc);

        setComponent(new Component());
        updateStatus(null);
    }

    public static void main(String[] args) {
        JFrame f = new JFrame("Test");
        f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        f.add(new ComponentPanel());
        f.pack();
        f.setVisible(true);
    }

    private void setComponent(Component c) {
        this.c = c;
        this.tfName.setText(c.name());
        this.taCtrl.setText(c.ctrl().prettyString());
        this.taPlant.setText(c.plant().prettyString());
        this.taPre.setText(c.pre().prettyString());
        this.taPost.setText(c.post().prettyString());

    }

    private void updateStatus(String status) {
        if (status != null) taStatus.setText(status);
        else if (c.isValid()) taStatus.setText(STATUS_VALID);
        else taStatus.setText(c.getInvalidMessage());
        taStatus.setCaretPosition(0);
    }

    @Override
    public void insertUpdate(DocumentEvent e) {
        changed(e.getDocument());
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        changed(e.getDocument());
    }

    private void changed(Document d) {
        String status = null;
        try {
            if (d == null) return;
            System.out.println("DOCUMENT CHANGED!");
            if (d.equals(tfName.getDocument())) {
                c.name_$eq(tfName.getText());
            } else if (d.equals(taCtrl.getDocument())) {
                c.ctrl_$eq(StringConverter.StringToStringConverter(taCtrl.getText()).asProgram());
            } else if (d.equals(taPlant.getDocument())) {
                c.plant_$eq((ODESystem) StringConverter.StringToStringConverter(taPlant.getText()).asProgram());
            } else if (d.equals(taPre.getDocument())) {
                c.pre_$eq(StringConverter.StringToStringConverter(taPre.getText()).asFormula());
            } else if (d.equals(taPost.getDocument())) {
                c.post_$eq(StringConverter.StringToStringConverter(taPost.getText()).asFormula());
            }
        } catch (Exception e) {
            e.printStackTrace();
            status = e.getMessage();
        }
        updateStatus(status);
    }

    @Override
    public void changedUpdate(DocumentEvent e) {
    }


}
